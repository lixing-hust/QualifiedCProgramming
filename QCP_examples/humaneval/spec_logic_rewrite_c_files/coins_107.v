Load "../spec/107".

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_107_pre_z (n : Z) : Prop :=
  problem_107_pre n.

Definition problem_107_spec_z (n : Z) (output : list Z) : Prop :=
  problem_107_spec n output.

Function base_digits_z_107 (n base : Z) {measure Z.to_nat n} : list Z :=
  if Z.leb base 1 then [48]
  else if Z.leb n 0 then [48]
  else if Z.ltb n base then [48 + n]
  else base_digits_z_107 (n / base) base ++ [48 + (n mod base)].
Proof.
  intros n base Hbase Hnpos Hnotlt.
  apply Z.leb_gt in Hbase.
  apply Z.leb_gt in Hnpos.
  apply Z.ltb_ge in Hnotlt.
  apply Z2Nat.inj_lt.
  - apply Z.div_pos; lia.
  - lia.
  - apply Z.div_lt; lia.
Defined.

Definition base_digits_pos_z_107 (n base : Z) : list Z :=
  if Z.leb n 0 then [] else base_digits_z_107 n base.

Definition decimal_chars_value_107 (digits : list Z) : Z :=
  fold_left (fun acc c => acc * 10 + (c - 48)) digits 0.

Definition reverse_digits_value_107 (n : Z) : Z :=
  decimal_chars_value_107 (rev (base_digits_z_107 n 10)).

Definition is_pal_result_107 (n : Z) : Z :=
  if Z.eqb (reverse_digits_value_107 n) n then 1 else 0.

Definition is_pal_bool_107 (n : Z) : bool :=
  Z.eqb (is_pal_result_107 n) 1.

Definition int_range_107 (n : Z) : Prop :=
  1 <= n <= 1000.

Definition palindrome_indices_107 (k : Z) : list Z :=
  map Z.of_nat (seq 1 (Z.to_nat k)).

Definition even_pal_term_107 (x : Z) : Z :=
  if andb (is_pal_bool_107 x) (Z.even x) then 1 else 0.

Definition odd_pal_term_107 (x : Z) : Z :=
  if andb (is_pal_bool_107 x) (negb (Z.even x)) then 1 else 0.

Definition count_even_pal_prefix_107 (k : Z) : Z :=
  fold_left Z.add (map even_pal_term_107 (palindrome_indices_107 k)) 0.

Definition count_odd_pal_prefix_107 (k : Z) : Z :=
  fold_left Z.add (map odd_pal_term_107 (palindrome_indices_107 k)) 0.

Definition pal_scan_state_107 (original t r : Z) : Prop :=
  exists suffix,
    0 < original /\
    0 <= t /\
    t <= original /\
    Forall (fun c => 48 <= c <= 57) suffix /\
    base_digits_z_107 original 10 =
      base_digits_pos_z_107 t 10 ++ suffix /\
    r = decimal_chars_value_107 (rev suffix).

Lemma decimal_chars_value_append_digit_107 : forall digits d,
  decimal_chars_value_107 (digits ++ [48 + d]) =
    decimal_chars_value_107 digits * 10 + d.
Proof.
  intros digits d.
  unfold decimal_chars_value_107.
  rewrite fold_left_app.
  change (fold_left (fun acc c : Z => acc * 10 + (c - 48)) digits 0 * 10 +
          (48 + d - 48) =
          fold_left (fun acc c : Z => acc * 10 + (c - 48)) digits 0 * 10 + d).
  lia.
Qed.

Lemma base_digits_pos_step_107 : forall n base,
  0 < n ->
  2 <= base ->
  base_digits_pos_z_107 n base =
    base_digits_pos_z_107 (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase.
  unfold base_digits_pos_z_107 at 1.
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite base_digits_z_107_equation.
  replace (base <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (n <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.ltb_spec n base) as [Hlt | Hge].
  - unfold base_digits_pos_z_107.
    replace (n / base <=? 0) with true.
    + rewrite app_nil_l.
      replace (n mod base) with n by (symmetry; apply Z.mod_small; lia).
      reflexivity.
    + symmetry. apply Z.leb_le.
      pose proof (Z.div_small n base ltac:(lia)).
      lia.
  - unfold base_digits_pos_z_107.
    replace (n / base <=? 0) with false.
    + reflexivity.
    + symmetry. apply Z.leb_gt.
      assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia).
      lia.
Qed.

Lemma base_digits_z_len_le4_107 : forall n,
  0 <= n <= 1000 ->
  (length (base_digits_z_107 n 10) <= 4)%nat.
Proof.
  intros n Hn.
  assert (Hnz : n = Z.of_nat (Z.to_nat n)) by lia.
  rewrite Hnz in *.
  set (m := Z.to_nat n) in *.
  assert (Hm : (m <= 1000)%nat) by lia.
  clearbody m.
  do 1001 (destruct m as [|m]; [vm_compute; lia |]).
  lia.
Qed.

Lemma decimal_chars_value_len4_bound_107 : forall digits,
  Forall (fun c => 48 <= c <= 57) digits ->
  (length digits <= 4)%nat ->
  0 <= decimal_chars_value_107 digits <= 9999.
Proof.
  intros digits Hdigits Hlen.
  destruct digits as [|a [|b [|c [|d [|e rest]]]]]; cbn in *; try lia;
    repeat match goal with
    | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
    end; cbn in *; lia.
Qed.

Lemma pal_scan_state_value_bound_107 : forall original t r,
  original <= 1000 ->
  pal_scan_state_107 original t r ->
  0 <= r <= 9999.
Proof.
  intros original t r Horig Hstate.
  destruct Hstate as [suffix [Hpos [Ht0 [Htle [Hsuf [Hdigits Hr]]]]]].
  subst r.
  apply decimal_chars_value_len4_bound_107.
  - rewrite Forall_forall in *.
    intros x Hx.
    apply Hsuf.
    apply in_rev in Hx; exact Hx.
  - rewrite length_rev.
    pose proof (base_digits_z_len_le4_107 original ltac:(lia)) as Hlen.
    rewrite Hdigits, length_app in Hlen.
    lia.
Qed.

Lemma pal_scan_init_107 : forall original,
  0 < original ->
  pal_scan_state_107 original original 0.
Proof.
  intros original Horig.
  exists (@nil Z).
  unfold base_digits_pos_z_107.
  replace (original <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  repeat split; try lia; try constructor.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma pal_scan_step_107 : forall original t r,
  pal_scan_state_107 original t r ->
  0 < t ->
  pal_scan_state_107 original (t / 10) (r * 10 + t mod 10).
Proof.
  intros original t r Hstate Ht.
  destruct Hstate as [suffix [Horig [Ht0 [Htle [Hsuf [Hdigits Hr]]]]]].
  exists ((48 + t mod 10) :: suffix).
  rewrite base_digits_pos_step_107 in Hdigits by lia.
  repeat split.
  - exact Horig.
  - apply Z.div_pos; lia.
  - assert (t / 10 <= t) by (apply Z.div_le_upper_bound; lia). lia.
  - constructor.
    + pose proof (Z.mod_pos_bound t 10 ltac:(lia)); lia.
    + exact Hsuf.
  - rewrite Hdigits. rewrite <- app_assoc. reflexivity.
  - change (rev ((48 + t mod 10) :: suffix))
      with (rev suffix ++ [48 + t mod 10]).
    rewrite decimal_chars_value_append_digit_107. subst r.
    pose proof (Z.mod_pos_bound t 10 ltac:(lia)); lia.
Qed.

Lemma pal_scan_step_quot_107 : forall original t r,
  pal_scan_state_107 original t r ->
  0 < t ->
  pal_scan_state_107 original (t ÷ 10) (r * 10 + t % 10).
Proof.
  intros original t r Hstate Ht.
  replace (t ÷ 10) with (t / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (t % 10) with (t mod 10) by (symmetry; apply Z.rem_mod_nonneg; lia).
  apply pal_scan_step_107; assumption.
Qed.

Lemma pal_scan_exit_107 : forall original t r,
  pal_scan_state_107 original t r ->
  t <= 0 ->
  r = reverse_digits_value_107 original.
Proof.
  intros original t r Hstate Ht.
  destruct Hstate as [suffix [Horig [Ht0 [Htle [Hsuf [Hdigits Hr]]]]]].
  assert (t = 0) by lia. subst t.
  unfold base_digits_pos_z_107 in Hdigits.
  cbn in Hdigits.
  subst r.
  unfold reverse_digits_value_107.
  rewrite Hdigits.
  reflexivity.
Qed.

Lemma palindrome_indices_snoc_107 : forall k,
  0 <= k ->
  palindrome_indices_107 (k + 1) = palindrome_indices_107 k ++ [k + 1].
Proof.
  intros k Hk.
  unfold palindrome_indices_107.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite seq_S.
  rewrite map_app.
  cbn.
  change (map Z.of_nat (seq 1 (Z.to_nat k)) ++
          [Z.of_nat (S (Z.to_nat k))] =
          map Z.of_nat (seq 1 (Z.to_nat k)) ++ [k + 1]).
  replace (Z.of_nat (S (Z.to_nat k))) with (k + 1) by lia.
  reflexivity.
Qed.

Lemma fold_left_Zadd_acc_107 : forall l acc,
  fold_left Z.add l acc = acc + fold_left Z.add l 0.
Proof.
  induction l as [|x xs IH]; intros acc.
  - cbn. lia.
  - cbn. rewrite IH. rewrite (IH x). lia.
Qed.

Lemma count_even_pal_prefix_step_107 : forall k,
  0 <= k ->
  count_even_pal_prefix_107 (k + 1) =
    count_even_pal_prefix_107 k + even_pal_term_107 (k + 1).
Proof.
  intros k Hk.
  unfold count_even_pal_prefix_107.
  rewrite palindrome_indices_snoc_107 by lia.
  rewrite map_app, fold_left_app.
  cbn.
  rewrite fold_left_Zadd_acc_107.
  lia.
Qed.

Lemma count_odd_pal_prefix_step_107 : forall k,
  0 <= k ->
  count_odd_pal_prefix_107 (k + 1) =
    count_odd_pal_prefix_107 k + odd_pal_term_107 (k + 1).
Proof.
  intros k Hk.
  unfold count_odd_pal_prefix_107.
  rewrite palindrome_indices_snoc_107 by lia.
  rewrite map_app, fold_left_app.
  cbn.
  rewrite fold_left_Zadd_acc_107.
  lia.
Qed.

Lemma count_even_pal_prefix_bounds_107 : forall k,
  0 <= k ->
  0 <= count_even_pal_prefix_107 k <= k.
Proof.
  intros k Hk.
  replace k with (Z.of_nat (Z.to_nat k)) by lia.
  induction (Z.to_nat k) as [|n IH].
  - cbn. lia.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite count_even_pal_prefix_step_107 by lia.
    unfold even_pal_term_107.
    destruct (andb _ _); lia.
Qed.

Lemma count_odd_pal_prefix_bounds_107 : forall k,
  0 <= k ->
  0 <= count_odd_pal_prefix_107 k <= k.
Proof.
  intros k Hk.
  replace k with (Z.of_nat (Z.to_nat k)) by lia.
  induction (Z.to_nat k) as [|n IH].
  - cbn. lia.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite count_odd_pal_prefix_step_107 by lia.
    unfold odd_pal_term_107.
    destruct (andb _ _); lia.
Qed.

Lemma is_pal_bool_matches_spec_107 : forall x,
  1 <= x <= 1000 ->
  is_pal_bool_107 x = is_palindrome_nat (Z.to_nat x).
Proof.
  intros x Hx.
  assert (Hxz : x = Z.of_nat (Z.to_nat x)) by lia.
  rewrite Hxz in *.
  set (m := Z.to_nat x) in *.
  assert (Hm : (1 <= m <= 1000)%nat) by lia.
  clearbody m.
  do 1001 (destruct m as [|m]; [vm_compute; reflexivity || lia |]).
  lia.
Qed.

Lemma Zeven_of_nat_107 : forall n,
  Z.even (Z.of_nat n) = Nat.even n.
Proof.
  intro n.
  destruct (Nat.even n) eqn:Hn.
  - apply Nat.even_spec in Hn.
    apply Z.even_spec.
    destruct Hn as [k Hk].
    exists (Z.of_nat k). lia.
  - destruct (Z.even (Z.of_nat n)) eqn:Hz; [| reflexivity].
    apply Z.even_spec in Hz.
    destruct Hz as [k Hk].
    assert (Nat.Even n) as Heven.
    { exists (Z.to_nat k). lia. }
    apply Nat.even_spec in Heven.
    rewrite Heven in Hn. discriminate.
Qed.

Lemma count_even_pal_upto_nat_step_107 : forall k,
  count_even_pal_upto_nat (S k) =
    count_even_pal_upto_nat k +
    (if andb (is_palindrome_nat (S k)) (Nat.even (S k)) then 1 else 0).
Proof.
  intro k.
  unfold count_even_pal_upto_nat.
  rewrite seq_S.
  replace (1 + k)%nat with (S k) by lia.
  rewrite filter_app, length_app.
  replace (length
             (filter (fun x : nat => andb (is_palindrome_nat x) (Nat.even x))
                [S k]))
    with (if andb (is_palindrome_nat (S k)) (Nat.even (S k)) then 1%nat else 0%nat)
    by (cbn; destruct (andb (is_palindrome_nat (S k))
                 match k with 0%nat => false | S n' => Nat.even n' end);
        reflexivity).
  rewrite Nat2Z.inj_add.
  destruct (andb (is_palindrome_nat (S k)) (Nat.even (S k))); reflexivity.
Qed.

Lemma count_odd_pal_upto_nat_step_107 : forall k,
  count_odd_pal_upto_nat (S k) =
    count_odd_pal_upto_nat k +
    (if andb (is_palindrome_nat (S k)) (negb (Nat.even (S k))) then 1 else 0).
Proof.
  intro k.
  unfold count_odd_pal_upto_nat.
  rewrite seq_S.
  replace (1 + k)%nat with (S k) by lia.
  rewrite filter_app, length_app.
  replace (length
             (filter
                (fun x : nat => andb (is_palindrome_nat x) (negb (Nat.even x)))
                [S k]))
    with (if andb (is_palindrome_nat (S k)) (negb (Nat.even (S k))) then 1%nat else 0%nat)
    by (cbn; destruct (andb (is_palindrome_nat (S k))
                 (negb match k with 0%nat => false | S n' => Nat.even n' end));
        reflexivity).
  rewrite Nat2Z.inj_add.
  destruct (andb (is_palindrome_nat (S k)) (negb (Nat.even (S k)))); reflexivity.
Qed.

Lemma count_even_pal_prefix_nat_spec_107 : forall k,
  (k <= 1000)%nat ->
  count_even_pal_prefix_107 (Z.of_nat k) = count_even_pal_upto_nat k.
Proof.
  induction k as [|k IH]; intros Hk.
  - reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) by lia.
    rewrite count_even_pal_prefix_step_107 by lia.
    rewrite IH by lia.
    rewrite count_even_pal_upto_nat_step_107.
    unfold even_pal_term_107.
    replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
    rewrite is_pal_bool_matches_spec_107 by lia.
    rewrite Zeven_of_nat_107.
    replace (Z.to_nat (Z.of_nat (S k))) with (S k) by lia.
    destruct (andb (is_palindrome_nat (S k)) (Nat.even (S k))); reflexivity.
Qed.

Lemma count_odd_pal_prefix_nat_spec_107 : forall k,
  (k <= 1000)%nat ->
  count_odd_pal_prefix_107 (Z.of_nat k) = count_odd_pal_upto_nat k.
Proof.
  induction k as [|k IH]; intros Hk.
  - reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) by lia.
    rewrite count_odd_pal_prefix_step_107 by lia.
    rewrite IH by lia.
    rewrite count_odd_pal_upto_nat_step_107.
    unfold odd_pal_term_107.
    replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
    rewrite is_pal_bool_matches_spec_107 by lia.
    rewrite Zeven_of_nat_107.
    replace (Z.to_nat (Z.of_nat (S k))) with (S k) by lia.
    destruct (andb (is_palindrome_nat (S k)) (negb (Nat.even (S k)))); reflexivity.
Qed.

Lemma problem_107_spec_z_of_counts : forall n,
  problem_107_pre_z n ->
  problem_107_spec_z n
    [count_even_pal_prefix_107 n; count_odd_pal_prefix_107 n].
Proof.
  intros n Hpre.
  unfold problem_107_pre_z, problem_107_pre in Hpre.
  unfold problem_107_spec_z, problem_107_spec.
  unfold count_even_pal_upto, count_odd_pal_upto.
  rewrite <- count_even_pal_prefix_nat_spec_107 by lia.
  rewrite <- count_odd_pal_prefix_nat_spec_107 by lia.
  replace (Z.of_nat (Z.to_nat n)) with n by lia.
  reflexivity.
Qed.
