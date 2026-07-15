Load "../spec/131".

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import IntLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_131_pre_z (n : Z) : Prop :=
  problem_131_pre (Z.to_nat n).

Definition problem_131_spec_z (n output : Z) : Prop :=
  0 <= output /\ problem_131_spec (Z.to_nat n) (Z.to_nat output).

Definition digit_at_131 (n p : nat) : nat :=
  (n / Nat.pow 10 p) mod 10.

Definition tail_odd_prod_nat_131 (n : nat) : nat :=
  product (filter Nat.odd (get_digits n)).

Definition digits_impl_z_131 (n : Z) : Z :=
  Z.of_nat (digits_impl (Z.to_nat n)).

Definition tail_odd_prod_z_131 (n : Z) : Z :=
  Z.of_nat (tail_odd_prod_nat_131 (Z.to_nat n)).

Definition digits_result_z_131 (n prod has : Z) : Z :=
  if Z.eqb has 0
  then digits_impl_z_131 n
  else prod * tail_odd_prod_z_131 n.

Definition digits_product_safe_z (n : Z) : Prop :=
  0 <= digits_impl_z_131 n <= INT_MAX.

Definition digits_state_z (original n prod has : Z) : Prop :=
  0 <= n /\
  0 <= prod /\
  (has = 0 \/ has = 1) /\
  (has = 0 -> prod = 1) /\
  digits_result_z_131 n prod has <= INT_MAX /\
  digits_result_z_131 n prod has = digits_impl_z_131 original.

Lemma Zquot_eq_Zdiv_nonneg_131 : forall a b,
  0 <= a ->
  0 < b ->
  Z.quot a b = a / b.
Proof.
  intros a b Ha Hb.
  apply Zquot_Zdiv_pos; lia.
Qed.

Lemma digit_at_tail_131 : forall k p,
  digit_at_131 k (S p) = digit_at_131 (k / 10) p.
Proof.
  intros k p.
  unfold digit_at_131.
  rewrite Nat.Div0.div_div.
  rewrite <- Nat.pow_succ_r'.
  reflexivity.
Qed.

Lemma digit_at_zero_large_131 : forall k p,
  (k <= p)%nat ->
  digit_at_131 k p = 0%nat.
Proof.
  intros k p Hkp.
  unfold digit_at_131.
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

Lemma filter_false_seq_131 : forall (f : nat -> bool) start len,
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

Lemma filter_odd_digit_at_false_seq_131 : forall k start len,
  (forall p, (start <= p < start + len)%nat ->
     Nat.odd (digit_at_131 k p) = false) ->
  filter Nat.odd (map (fun p => digit_at_131 k p) (seq start len)) = [].
Proof.
  intros k start len Hfalse.
  revert start Hfalse.
  induction len; intros start Hfalse; simpl.
  - reflexivity.
  - rewrite Hfalse by lia.
    apply IHlen.
    intros p Hp.
    apply Hfalse.
    lia.
Qed.

Lemma filter_odd_get_digits_tail_131 : forall k len,
  (k <= len)%nat ->
  filter Nat.odd (map (fun p => digit_at_131 k p) (seq 0 len)) =
  filter Nat.odd (get_digits k).
Proof.
  intros k len Hk.
  unfold get_digits.
  replace len with (k + (len - k))%nat by lia.
  rewrite seq_app, map_app, filter_app.
  replace (0 + k)%nat with k by lia.
  rewrite (filter_odd_digit_at_false_seq_131 k k (len - k)).
  - rewrite app_nil_r. reflexivity.
  - intros p Hp.
    rewrite digit_at_zero_large_131 by lia.
    reflexivity.
Qed.

Lemma filter_odd_get_digits_step_131 : forall n,
  (0 < n)%nat ->
  filter Nat.odd (get_digits n) =
    (if Nat.odd (n mod 10)
     then (n mod 10)%nat :: filter Nat.odd (get_digits (n / 10)%nat)
     else filter Nat.odd (get_digits (n / 10)%nat)).
Proof.
  intros n Hn.
  destruct n as [|n']; [lia|].
  unfold get_digits at 1.
  change (seq 0 (S n')) with (0%nat :: seq 1 n').
  cbn [map filter].
  change (10 ^ 0)%nat with 1%nat.
  rewrite Nat.div_1_r.
  rewrite <- seq_shift.
  rewrite map_map.
  replace (map (fun x : nat => ((S n' / 10 ^ S x) mod 10)%nat) (seq 0 n'))
    with (map (digit_at_131 (S n' / 10)%nat) (seq 0 n')).
  2:{
    apply map_ext.
    intro p.
    unfold digit_at_131.
    rewrite Nat.Div0.div_div.
    rewrite <- Nat.pow_succ_r'.
    reflexivity.
  }
  rewrite <- (filter_odd_get_digits_tail_131 (S n' / 10)%nat n').
  - destruct (Nat.odd (S n' mod 10)); reflexivity.
  - assert (S n' / 10 < S n')%nat by (apply Nat.div_lt; lia).
    lia.
Qed.

Lemma fold_left_mul_acc_131 : forall l acc,
  fold_left Nat.mul l acc = (acc * fold_left Nat.mul l 1)%nat.
Proof.
  induction l as [|a l IH]; intros acc; simpl.
  - lia.
  - rewrite (IH (acc * a)%nat).
    replace (a + 0)%nat with a by lia.
    replace (fold_left Nat.mul l a) with (a * fold_left Nat.mul l 1)%nat
      by (symmetry; apply IH).
    lia.
Qed.

Lemma product_cons_131 : forall a l,
  product (a :: l) = (a * product l)%nat.
Proof.
  intros a l.
  unfold product.
  simpl.
  replace (a + 0)%nat with a by lia.
  rewrite fold_left_mul_acc_131.
  reflexivity.
Qed.

Lemma tail_odd_prod_step_odd_131 : forall n,
  (0 < n)%nat ->
  Nat.odd (n mod 10) = true ->
  tail_odd_prod_nat_131 n =
    ((n mod 10) * tail_odd_prod_nat_131 (n / 10))%nat.
Proof.
  intros n Hn Hodd.
  unfold tail_odd_prod_nat_131.
  rewrite filter_odd_get_digits_step_131 by exact Hn.
  rewrite Hodd.
  apply product_cons_131.
Qed.

Lemma tail_odd_prod_step_even_131 : forall n,
  (0 < n)%nat ->
  Nat.odd (n mod 10) = false ->
  tail_odd_prod_nat_131 n = tail_odd_prod_nat_131 (n / 10).
Proof.
  intros n Hn Heven.
  unfold tail_odd_prod_nat_131.
  rewrite filter_odd_get_digits_step_131 by exact Hn.
  rewrite Heven.
  reflexivity.
Qed.

Lemma digits_impl_step_odd_131 : forall n,
  (0 < n)%nat ->
  Nat.odd (n mod 10) = true ->
  digits_impl n =
    ((n mod 10) * tail_odd_prod_nat_131 (n / 10))%nat.
Proof.
  intros n Hn Hodd.
  unfold digits_impl.
  rewrite filter_odd_get_digits_step_131 by exact Hn.
  rewrite Hodd.
  apply product_cons_131.
Qed.

Lemma digits_impl_step_even_131 : forall n,
  (0 < n)%nat ->
  Nat.odd (n mod 10) = false ->
  digits_impl n = digits_impl (n / 10).
Proof.
  intros n Hn Heven.
  unfold digits_impl.
  rewrite filter_odd_get_digits_step_131 by exact Hn.
  rewrite Heven.
  reflexivity.
Qed.

Lemma zrem10_nat_131 : forall n,
  0 <= n ->
  Z.to_nat (Z.rem n 10) = (Z.to_nat n mod 10)%nat.
Proof.
  intros n Hn.
  rewrite Z.rem_mod_nonneg by lia.
  replace 10%nat with (Z.to_nat 10) by reflexivity.
  rewrite <- Z2Nat.inj_mod by lia.
  reflexivity.
Qed.

Lemma zquot10_nat_131 : forall n,
  0 <= n ->
  Z.to_nat (Z.quot n 10) = (Z.to_nat n / 10)%nat.
Proof.
  intros n Hn.
  rewrite Zquot_eq_Zdiv_nonneg_131 by lia.
  rewrite Z2Nat.inj_div by lia.
  reflexivity.
Qed.

Lemma zquot10_nonneg_131 : forall n,
  0 <= n ->
  0 <= Z.quot n 10.
Proof.
  intros n Hn.
  rewrite Zquot_eq_Zdiv_nonneg_131 by lia.
  apply Z.div_pos; lia.
Qed.

Lemma zquot10_le_self_131 : forall n,
  0 <= n ->
  Z.quot n 10 <= n.
Proof.
  intros n Hn.
  rewrite Zquot_eq_Zdiv_nonneg_131 by lia.
  pose proof (Z.div_pos n 10 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod n 10 ltac:(lia)).
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
  nia.
Qed.

Lemma z_odd_nat_odd_131 : forall d,
  0 <= d < 10 ->
  Z.rem d 2 = 1 ->
  Nat.odd (Z.to_nat d) = true.
Proof.
  intros d Hd Hrem.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
          d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  end; subst; vm_compute in *; congruence.
Qed.

Lemma z_not_odd_nat_even_131 : forall d,
  0 <= d < 10 ->
  Z.rem d 2 <> 1 ->
  Nat.odd (Z.to_nat d) = false.
Proof.
  intros d Hd Hrem.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
          d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  end; subst; vm_compute in *; try congruence.
Qed.

Lemma tail_odd_prod_z_step_odd_131 : forall n,
  n > 0 ->
  Z.rem (Z.rem n 10) 2 = 1 ->
  tail_odd_prod_z_131 n =
    Z.rem n 10 * tail_odd_prod_z_131 (Z.quot n 10).
Proof.
  intros n Hn Hodd.
  unfold tail_odd_prod_z_131.
  rewrite zquot10_nat_131 by lia.
  rewrite (tail_odd_prod_step_odd_131 (Z.to_nat n)).
  - rewrite Nat2Z.inj_mul.
    rewrite <- zrem10_nat_131 by lia.
    rewrite Z2Nat.id by (apply Z.rem_nonneg; lia).
    reflexivity.
  - lia.
  - rewrite <- zrem10_nat_131 by lia.
    apply z_odd_nat_odd_131.
    + apply Z.rem_bound_pos; lia.
    + exact Hodd.
Qed.

Lemma tail_odd_prod_z_step_even_131 : forall n,
  n > 0 ->
  Z.rem (Z.rem n 10) 2 <> 1 ->
  tail_odd_prod_z_131 n =
    tail_odd_prod_z_131 (Z.quot n 10).
Proof.
  intros n Hn Heven.
  unfold tail_odd_prod_z_131.
  rewrite zquot10_nat_131 by lia.
  rewrite (tail_odd_prod_step_even_131 (Z.to_nat n)).
  - reflexivity.
  - lia.
  - rewrite <- zrem10_nat_131 by lia.
    apply z_not_odd_nat_even_131.
    + apply Z.rem_bound_pos; lia.
    + exact Heven.
Qed.

Lemma digits_impl_z_step_odd_131 : forall n,
  n > 0 ->
  Z.rem (Z.rem n 10) 2 = 1 ->
  digits_impl_z_131 n =
    Z.rem n 10 * tail_odd_prod_z_131 (Z.quot n 10).
Proof.
  intros n Hn Hodd.
  unfold digits_impl_z_131, tail_odd_prod_z_131.
  rewrite zquot10_nat_131 by lia.
  rewrite (digits_impl_step_odd_131 (Z.to_nat n)).
  - rewrite Nat2Z.inj_mul.
    rewrite <- zrem10_nat_131 by lia.
    rewrite Z2Nat.id by (apply Z.rem_nonneg; lia).
    reflexivity.
  - lia.
  - rewrite <- zrem10_nat_131 by lia.
    apply z_odd_nat_odd_131.
    + apply Z.rem_bound_pos; lia.
    + exact Hodd.
Qed.

Lemma digits_impl_z_step_even_131 : forall n,
  n > 0 ->
  Z.rem (Z.rem n 10) 2 <> 1 ->
  digits_impl_z_131 n = digits_impl_z_131 (Z.quot n 10).
Proof.
  intros n Hn Heven.
  unfold digits_impl_z_131.
  rewrite zquot10_nat_131 by lia.
  rewrite (digits_impl_step_even_131 (Z.to_nat n)).
  - reflexivity.
  - lia.
  - rewrite <- zrem10_nat_131 by lia.
    apply z_not_odd_nat_even_131.
    + apply Z.rem_bound_pos; lia.
    + exact Heven.
Qed.

Lemma tail_odd_prod_z_nonneg_131 : forall n,
  0 <= tail_odd_prod_z_131 n.
Proof.
  intros n.
  unfold tail_odd_prod_z_131.
  lia.
Qed.

Lemma product_filter_odd_ge1_131 : forall l,
  (1 <= product (filter Nat.odd l))%nat.
Proof.
  induction l as [|a l IH]; simpl.
  - unfold product. simpl. lia.
  - destruct (Nat.odd a) eqn:Hodd.
    + rewrite product_cons_131.
      destruct a; simpl in Hodd; try discriminate.
      nia.
    + exact IH.
Qed.

Lemma tail_odd_prod_z_ge1_131 : forall n,
  1 <= tail_odd_prod_z_131 n.
Proof.
  intros n.
  unfold tail_odd_prod_z_131, tail_odd_prod_nat_131.
  change 1 with (Z.of_nat 1).
  apply Nat2Z.inj_le.
  apply product_filter_odd_ge1_131.
Qed.

Lemma digits_state_init_131 : forall n,
  0 <= n ->
  digits_product_safe_z n ->
  digits_state_z n n 1 0.
Proof.
  intros n Hn Hsafe.
  unfold digits_state_z, digits_product_safe_z, digits_result_z_131 in *.
  rewrite Z.eqb_refl.
  repeat split; try lia.
Qed.

Lemma digits_state_step_odd_131 : forall original n prod has,
  n > 0 ->
  Z.rem (Z.rem n 10) 2 = 1 ->
  digits_state_z original n prod has ->
  digits_state_z original (Z.quot n 10) (prod * Z.rem n 10) 1.
Proof.
  intros original n prod has Hn Hodd Hstate.
  unfold digits_state_z in *.
  destruct Hstate as [Hn0 [Hprod [Hhas [Hprod0 [Hbound Heq]]]]].
  assert (Hd_bounds : 0 <= Z.rem n 10 < 10) by (apply Z.rem_bound_pos; lia).
  assert (Hq_nonneg : 0 <= Z.quot n 10).
  { rewrite Zquot_eq_Zdiv_nonneg_131 by lia. apply Z.div_pos; lia. }
  repeat split; try lia.
  - unfold digits_result_z_131 in *.
    destruct Hhas as [Hzero | Hone].
    + subst has.
      rewrite Z.eqb_refl in Hbound.
      rewrite digits_impl_z_step_odd_131 in Hbound by assumption.
      specialize (Hprod0 eq_refl).
      subst prod.
      change (1 =? 0) with false.
      ring_simplify.
      lia.
    + subst has.
      rewrite tail_odd_prod_z_step_odd_131 in Hbound by assumption.
      change (1 =? 0) with false.
      replace (prod * (Z.rem n 10 * tail_odd_prod_z_131 (Z.quot n 10)))
        with (prod * Z.rem n 10 * tail_odd_prod_z_131 (Z.quot n 10)) in Hbound
        by ring.
      exact Hbound.
  - unfold digits_result_z_131 in *.
    destruct Hhas as [Hzero | Hone].
    + subst has.
      rewrite Z.eqb_refl in Heq.
      rewrite digits_impl_z_step_odd_131 in Heq by assumption.
      change (1 =? 0) with false.
      rewrite <- Heq.
      specialize (Hprod0 eq_refl).
      subst prod.
      ring_simplify.
      reflexivity.
    + subst has.
      rewrite tail_odd_prod_z_step_odd_131 in Heq by assumption.
      change (1 =? 0) with false in Heq.
      replace (prod * (Z.rem n 10 * tail_odd_prod_z_131 (Z.quot n 10)))
        with (prod * Z.rem n 10 * tail_odd_prod_z_131 (Z.quot n 10)) in Heq
        by ring.
      change (1 =? 0) with false.
      rewrite <- Heq.
      ring_simplify.
      reflexivity.
Qed.

Lemma digits_state_step_even_131 : forall original n prod has,
  n > 0 ->
  Z.rem (Z.rem n 10) 2 <> 1 ->
  digits_state_z original n prod has ->
  digits_state_z original (Z.quot n 10) prod has.
Proof.
  intros original n prod has Hn Heven Hstate.
  unfold digits_state_z in *.
  destruct Hstate as [Hn0 [Hprod [Hhas [Hprod0 [Hbound Heq]]]]].
  assert (Hq_nonneg : 0 <= Z.quot n 10).
  { rewrite Zquot_eq_Zdiv_nonneg_131 by lia. apply Z.div_pos; lia. }
  repeat split; try lia; try exact Hhas; try exact Hprod0.
  - unfold digits_result_z_131 in *.
    destruct Hhas as [Hzero | Hone].
    + subst has.
      repeat rewrite Z.eqb_refl in *.
      rewrite <- digits_impl_z_step_even_131 by assumption.
      exact Hbound.
    + subst has.
      repeat rewrite Z.eqb_neq in * by lia.
      rewrite <- tail_odd_prod_z_step_even_131 by assumption.
      exact Hbound.
  - unfold digits_result_z_131 in *.
    destruct Hhas as [Hzero | Hone].
    + subst has.
      repeat rewrite Z.eqb_refl in *.
      rewrite <- digits_impl_z_step_even_131 by assumption.
      exact Heq.
    + subst has.
      repeat rewrite Z.eqb_neq in * by lia.
      rewrite <- tail_odd_prod_z_step_even_131 by assumption.
      exact Heq.
Qed.

Lemma digits_state_odd_product_bound_131 : forall original n prod has,
  n > 0 ->
  Z.rem (Z.rem n 10) 2 = 1 ->
  digits_state_z original n prod has ->
  prod * Z.rem n 10 <= INT_MAX.
Proof.
  intros original n prod has Hn Hodd Hstate.
  unfold digits_state_z in Hstate.
  destruct Hstate as [Hn0 [Hprod [Hhas [Hprod0 [Hbound _]]]]].
  assert (Hd_bounds : 0 <= Z.rem n 10 < 10) by (apply Z.rem_bound_pos; lia).
  destruct Hhas as [Hzero | Hone].
  - subst has.
    specialize (Hprod0 eq_refl).
    subst prod.
    lia.
  - subst has.
    unfold digits_result_z_131 in Hbound.
    change (1 =? 0) with false in Hbound.
    rewrite tail_odd_prod_z_step_odd_131 in Hbound by assumption.
    set (tail := tail_odd_prod_z_131 (Z.quot n 10)) in *.
    assert (Htail : 1 <= tail).
    { subst tail. apply tail_odd_prod_z_ge1_131. }
    assert (Hpd_nonneg : 0 <= prod * Z.rem n 10) by nia.
    assert (Hle : prod * Z.rem n 10 <= prod * Z.rem n 10 * tail).
    {
      replace (prod * Z.rem n 10) with (prod * Z.rem n 10 * 1) at 1 by ring.
      apply Z.mul_le_mono_nonneg_l; lia.
    }
    replace (prod * (Z.rem n 10 * tail))
      with (prod * Z.rem n 10 * tail) in Hbound by ring.
    lia.
Qed.

Lemma digits_state_done_some_131 : forall original prod,
  digits_state_z original 0 prod 1 ->
  problem_131_spec_z original prod.
Proof.
  intros original prod Hstate.
  unfold digits_state_z, digits_result_z_131 in Hstate.
  destruct Hstate as [_ [Hprod [_ [_ [_ Heq]]]]].
  change (1 =? 0) with false in Heq.
  unfold tail_odd_prod_z_131, tail_odd_prod_nat_131, get_digits in Heq.
  simpl in Heq.
  unfold digits_impl_z_131 in Heq.
  ring_simplify in Heq.
  unfold problem_131_spec_z, problem_131_spec.
  split; [lia|].
  rewrite Heq.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma digits_state_done_none_131 : forall original prod,
  digits_state_z original 0 prod 0 ->
  problem_131_spec_z original 0.
Proof.
  intros original prod Hstate.
  unfold digits_state_z, digits_result_z_131 in Hstate.
  destruct Hstate as [_ [_ [_ [_ [_ Heq]]]]].
  rewrite Z.eqb_refl in Heq.
  unfold problem_131_spec_z, problem_131_spec.
  split; [lia|].
  unfold digits_impl_z_131 in Heq.
  simpl in Heq.
  change 0 with (Z.of_nat 0) in Heq.
  apply Nat2Z.inj in Heq.
  exact Heq.
Qed.
