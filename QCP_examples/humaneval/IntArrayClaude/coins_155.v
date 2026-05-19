Load "../spec/155".

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Lists.List.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition Zabs (x : Z) : Z := Z.abs x.

Fixpoint c_digits_fuel (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S fuel' =>
      let p := Z.abs n in
      if p =? 0 then nil else Z.rem p 10 :: c_digits_fuel fuel' (Z.quot p 10)
  end.

Definition c_digits (n : Z) : list Z :=
  if Z.abs n =? 0
  then [0]
  else c_digits_fuel (Z.to_nat (Z.abs n) + 1)%nat (Z.abs n).

Fixpoint count_digits_c (digits : list Z) (even odd : Z) : Z * Z :=
  match digits with
  | nil => (even, odd)
  | d :: rest =>
      if Z.eqb (Z.rem d 2) 1
      then count_digits_c rest even (odd + 1)
      else count_digits_c rest (even + 1) odd
  end.

Definition count_result_c (num : Z) : Z * Z :=
  count_digits_c (c_digits num) 0 0.

Definition digit_count_state (num w even odd : Z) : Prop :=
  0 <= w /\
  0 <= even /\
  0 <= odd /\
  exists fuel,
    (w = 0 \/ w < Z.of_nat fuel) /\
    count_digits_c (c_digits_fuel fuel w) even odd = count_result_c num /\
    even + odd + Zlength (c_digits_fuel fuel w) <= Z.abs num + 1.

Definition problem_155_pre_z (num : Z) : Prop :=
  problem_155_pre num.

Definition problem_155_spec_z (num : Z) (output : list Z) : Prop :=
  exists even odd,
    output = [Z.of_nat even; Z.of_nat odd] /\
    problem_155_spec num (even, odd).

Lemma c_digits_fuel_to_digits_fuel_nonzero : forall fuel n,
  0 <= n ->
  c_digits_fuel fuel n = to_digits_fuel_nonzero fuel n.
Proof.
  induction fuel as [|fuel IH]; intros n Hn; simpl; [reflexivity|].
  rewrite Z.abs_eq by lia.
  destruct (n =? 0) eqn:Hzero; [reflexivity|].
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.quot_div_nonneg by lia.
  rewrite IH by (apply Z.div_pos; lia).
  reflexivity.
Qed.

Lemma to_digits_fuel_nonzero_abs : forall fuel n,
  to_digits_fuel_nonzero fuel (Z.abs n) = to_digits_fuel_nonzero fuel n.
Proof.
  destruct fuel as [|fuel]; intros n; simpl; [reflexivity|].
  rewrite Z.abs_eq by apply Z.abs_nonneg.
  reflexivity.
Qed.

Lemma c_digits_to_digits : forall n,
  c_digits n = to_digits n.
Proof.
  intros n.
  unfold c_digits, to_digits.
  destruct (Z.abs n =? 0) eqn:Habs; [reflexivity|].
  rewrite c_digits_fuel_to_digits_fuel_nonzero by apply Z.abs_nonneg.
  apply to_digits_fuel_nonzero_abs.
Qed.

Lemma count_digits_c_to_count_digits_acc : forall digits even odd,
  (forall d, In d digits -> 0 <= d) ->
  count_digits_c digits (Z.of_nat even) (Z.of_nat odd) =
  let '(even', odd') := count_digits_acc digits (even, odd) in
  (Z.of_nat even', Z.of_nat odd').
Proof.
  induction digits as [|d rest IH]; intros even odd Hnonneg; simpl.
  - reflexivity.
  - assert (Hd_nonneg : 0 <= d) by (apply Hnonneg; simpl; auto).
    rewrite Z.rem_mod_nonneg by lia.
    rewrite Zmod_odd.
    rewrite <- Z.negb_even.
    destruct (Z.even d) eqn:Heven.
    + simpl.
      replace (Z.of_nat even + 1) with (Z.of_nat (S even)) by lia.
      apply IH.
      intros x Hx. apply Hnonneg. simpl. auto.
    + simpl.
      replace (Z.of_nat odd + 1) with (Z.of_nat (S odd)) by lia.
      apply IH.
      intros x Hx. apply Hnonneg. simpl. auto.
Qed.

Lemma c_digits_fuel_nonnegative : forall fuel n d,
  0 <= n ->
  In d (c_digits_fuel fuel n) ->
  0 <= d.
Proof.
  induction fuel as [|fuel IH]; intros n d Hn Hin; simpl in Hin; [contradiction|].
  rewrite Z.abs_eq in Hin by lia.
  destruct (n =? 0) eqn:Hzero; [contradiction|].
  simpl in Hin.
  destruct Hin as [Hd | Hin].
  - subst d. apply Z.rem_bound_pos; lia.
  - apply IH in Hin.
    + exact Hin.
    + rewrite Z.quot_div_nonneg by lia.
      apply Z.div_pos; lia.
Qed.

Lemma c_digits_nonnegative : forall n d,
  In d (c_digits n) ->
  0 <= d.
Proof.
  intros n d Hin.
  unfold c_digits in Hin.
  destruct (Z.abs n =? 0) eqn:Habs.
  - simpl in Hin. destruct Hin as [-> | []]. lia.
  - eapply c_digits_fuel_nonnegative; eauto.
    apply Z.abs_nonneg.
Qed.

Lemma count_result_c_to_even_odd_count_impl : forall num,
  count_result_c num =
  let '(even, odd) := even_odd_count_impl num in
  (Z.of_nat even, Z.of_nat odd).
Proof.
  intros num.
  unfold count_result_c, even_odd_count_impl.
  rewrite <- c_digits_to_digits.
  change 0 with (Z.of_nat O).
  apply count_digits_c_to_count_digits_acc.
  apply c_digits_nonnegative.
Qed.

Lemma c_digits_fuel_length_bound : forall fuel n,
  Zlength (c_digits_fuel fuel n) <= Z.of_nat fuel.
Proof.
  intros fuel.
  induction fuel as [|fuel IH]; intros n; simpl; [rewrite Zlength_nil; lia|].
  destruct (Z.abs n =? 0).
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    pose proof (IH (Z.quot (Z.abs n) 10)).
    lia.
Qed.

Lemma digit_count_state_init_zero : forall num,
  Z.abs num = 0 ->
  digit_count_state num 0 1 0.
Proof.
  intros num Habs.
  unfold digit_count_state, count_result_c, c_digits.
  rewrite Habs.
  simpl.
  repeat split; try lia.
  exists O.
  split; [left; lia|].
  split; [reflexivity|].
  rewrite Zlength_nil; lia.
Qed.

Lemma digit_count_state_init_nonzero : forall num,
  0 < Z.abs num ->
  digit_count_state num (Z.abs num) 0 0.
Proof.
  intros num Habs.
  unfold digit_count_state, count_result_c, c_digits.
  destruct (Z.abs num =? 0) eqn:Hz; [apply Z.eqb_eq in Hz; lia|].
  repeat split; try lia.
  exists (Z.to_nat (Z.abs num) + 1)%nat.
  split.
  - right.
    rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    simpl.
    lia.
  - split; [reflexivity|].
    pose proof (c_digits_fuel_length_bound
      (Z.to_nat (Z.abs num) + 1)%nat (Z.abs num)).
    rewrite Nat2Z.inj_add in H.
    rewrite Z2Nat.id in H by lia.
    simpl in H.
    lia.
Qed.

Lemma c_digits_fuel_step : forall fuel w,
  0 < w ->
  w < Z.of_nat fuel ->
  c_digits_fuel fuel w =
    Z.rem w 10 :: c_digits_fuel (Nat.pred fuel) (Z.quot w 10).
Proof.
  intros fuel w Hw Hfuel.
  destruct fuel as [|fuel']; [simpl in Hfuel; lia|].
  simpl.
  rewrite Z.abs_eq by lia.
  destruct (w =? 0) eqn:Hz; [apply Z.eqb_eq in Hz; lia|].
  reflexivity.
Qed.

Lemma Zquot_10_lt_self : forall w,
  0 < w ->
  Z.quot w 10 < w.
Proof.
  intros w Hw.
  rewrite Z.quot_div_nonneg by lia.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma digit_count_state_odd_next_bound : forall num w even odd bound,
  digit_count_state num w even odd ->
  0 < w ->
  Z.abs num + 1 < bound ->
  odd + 1 < bound.
Proof.
  intros num w even odd bound Hstate Hw Hbound.
  unfold digit_count_state in Hstate.
  destruct Hstate as [_ [He_lo [Ho_lo [fuel [Hfuel [_ Hlen]]]]]].
  assert (Hfuel_pos : w < Z.of_nat fuel) by lia.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hlen.
  rewrite Zlength_cons in Hlen.
  unfold Zabs in Hlen.
  pose proof (Zlength_nonneg (c_digits_fuel (Nat.pred fuel) (w ÷ 10))).
  lia.
Qed.

Lemma digit_count_state_even_next_bound : forall num w even odd bound,
  digit_count_state num w even odd ->
  0 < w ->
  Z.abs num + 1 < bound ->
  even + 1 < bound.
Proof.
  intros num w even odd bound Hstate Hw Hbound.
  unfold digit_count_state in Hstate.
  destruct Hstate as [_ [He_lo [Ho_lo [fuel [Hfuel [_ Hlen]]]]]].
  assert (Hfuel_pos : w < Z.of_nat fuel) by lia.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hlen.
  rewrite Zlength_cons in Hlen.
  unfold Zabs in Hlen.
  pose proof (Zlength_nonneg (c_digits_fuel (Nat.pred fuel) (w ÷ 10))).
  lia.
Qed.

Lemma digit_count_state_step_odd : forall num w even odd d,
  digit_count_state num w even odd ->
  0 < w ->
  d = Z.rem w 10 ->
  Z.rem d 2 = 1 ->
  digit_count_state num (Z.quot w 10) even (odd + 1).
Proof.
  intros num w even odd d Hstate Hw Hd Hodd.
  unfold digit_count_state in *.
  destruct Hstate as [Hw_nonneg [He_lo [Ho_lo [fuel [Hfuel [Hrun Hlen]]]]]].
  assert (Hfuel_pos : w < Z.of_nat fuel) by lia.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hrun.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hlen.
  subst d.
  destruct (Z.rem (Z.rem w 10) 2 =? 1) eqn:Hpar;
    [| apply Z.eqb_neq in Hpar; lia].
  simpl in Hrun.
  rewrite Hpar in Hrun.
  split.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
  - split; [lia|].
    split; [lia|].
    exists (Nat.pred fuel).
    split.
    + destruct (Z.eq_dec (Z.quot w 10) 0) as [Hzero | Hnz].
      * left; lia.
      * right.
        destruct fuel as [|fuel']; [simpl in Hfuel_pos; lia|].
        simpl.
        rewrite Nat2Z.inj_succ in Hfuel_pos.
        pose proof (Zquot_10_lt_self w Hw).
        lia.
    + split; [exact Hrun|].
      rewrite Zlength_cons in Hlen.
      lia.
Qed.

Lemma digit_count_state_step_even : forall num w even odd d,
  digit_count_state num w even odd ->
  0 < w ->
  d = Z.rem w 10 ->
  Z.rem d 2 <> 1 ->
  digit_count_state num (Z.quot w 10) (even + 1) odd.
Proof.
  intros num w even odd d Hstate Hw Hd Heven.
  unfold digit_count_state in *.
  destruct Hstate as [Hw_nonneg [He_lo [Ho_lo [fuel [Hfuel [Hrun Hlen]]]]]].
  assert (Hfuel_pos : w < Z.of_nat fuel) by lia.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hrun.
  rewrite (c_digits_fuel_step fuel w Hw Hfuel_pos) in Hlen.
  subst d.
  destruct (Z.rem (Z.rem w 10) 2 =? 1) eqn:Hpar;
    [apply Z.eqb_eq in Hpar; lia|].
  simpl in Hrun.
  rewrite Hpar in Hrun.
  split.
  - rewrite Z.quot_div_nonneg by lia.
    apply Z.div_pos; lia.
  - split; [lia|].
    split; [lia|].
    exists (Nat.pred fuel).
    split.
    + destruct (Z.eq_dec (Z.quot w 10) 0) as [Hzero | Hnz].
      * left; lia.
      * right.
        destruct fuel as [|fuel']; [simpl in Hfuel_pos; lia|].
        simpl.
        rewrite Nat2Z.inj_succ in Hfuel_pos.
        pose proof (Zquot_10_lt_self w Hw).
        lia.
    + split; [exact Hrun|].
      rewrite Zlength_cons in Hlen.
      lia.
Qed.

Lemma digit_count_state_final_spec : forall num even odd,
  digit_count_state num 0 even odd ->
  problem_155_spec_z num [even; odd].
Proof.
  intros num even odd Hstate.
  unfold digit_count_state in Hstate.
  destruct Hstate as [_ [Heven_nonneg [Hodd_nonneg [fuel [_ [Hrun _]]]]]].
  unfold problem_155_spec_z.
  exists (Z.to_nat even), (Z.to_nat odd).
  split.
  - rewrite Z2Nat.id by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - unfold problem_155_spec.
    pose proof (count_result_c_to_even_odd_count_impl num) as Horig.
    destruct (even_odd_count_impl num) as [even_nat odd_nat] eqn:Himpl.
    destruct fuel; simpl in Hrun; symmetry in Hrun.
    + rewrite Hrun in Horig.
      injection Horig as He Ho.
      apply f_equal with (f := Z.to_nat) in He.
      apply f_equal with (f := Z.to_nat) in Ho.
      rewrite Nat2Z.id in He, Ho.
      rewrite He, Ho.
      reflexivity.
    + rewrite Hrun in Horig.
      injection Horig as He Ho.
      apply f_equal with (f := Z.to_nat) in He.
      apply f_equal with (f := Z.to_nat) in Ho.
      rewrite Nat2Z.id in He, Ho.
      rewrite He, Ho.
      reflexivity.
Qed.
