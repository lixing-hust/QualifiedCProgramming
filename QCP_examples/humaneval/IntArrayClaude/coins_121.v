Load "../spec/121".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint sum_odd_at_even_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := sum_odd_at_even_upto_nat n' l in
      let i := Z.of_nat n' in
      let x := Znth (2 * i) l 0 in
      if Z.eqb (Z.rem x 2) 1 then s + x else s
  end.

Definition sum_odd_at_even_upto (i : Z) (l : list Z) : Z :=
  sum_odd_at_even_upto_nat (Z.to_nat i) l.

Definition problem_121_pre_z (lst : list Z) : Prop :=
  lst <> [].

Definition problem_121_spec_z (lst : list Z) (output : Z) : Prop :=
  exists output_nat,
    output = Z.of_nat output_nat /\
    problem_121_spec (map Z.to_nat lst) output_nat.

Definition odd_even_position_add_z (x : Z) : Z :=
  if Z.eqb (Z.rem x 2) 1 then x else 0.

Fixpoint sum_odd_in_even_positions_z (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: [] => odd_even_position_add_z x
  | x :: _ :: rest => odd_even_position_add_z x + sum_odd_in_even_positions_z rest
  end.

Fixpoint sum_odd_in_even_positions_nat (l : list nat) : nat :=
  match l with
  | [] => O
  | x :: [] => if Nat.odd x then x else O
  | x :: _ :: rest => (if Nat.odd x then x else O) + sum_odd_in_even_positions_nat rest
  end.

Definition sum_odd_at_even_int_range (lst : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i < Zlength lst ->
    INT_MIN <= sum_odd_at_even_upto i lst <= INT_MAX /\
    INT_MIN <= sum_odd_at_even_upto i lst + Znth (2 * i) lst 0 <= INT_MAX.

Lemma sum_odd_at_even_upto_0 : forall l,
  sum_odd_at_even_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_odd_at_even_upto.
  reflexivity.
Qed.

Lemma sum_odd_at_even_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i) l 0) 2 = 1 ->
  sum_odd_at_even_upto (i + 1) l =
  sum_odd_at_even_upto i l + Znth (2 * i) l 0.
Proof.
  intros i l Hi Hodd.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  destruct (Z.eqb (Z.rem (Znth (2 * i) l 0) 2) 1) eqn:Heq.
  - reflexivity.
  - apply Z.eqb_neq in Heq. congruence.
Qed.

Lemma sum_odd_at_even_upto_step_not_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i) l 0) 2 <> 1 ->
  sum_odd_at_even_upto (i + 1) l =
  sum_odd_at_even_upto i l.
Proof.
  intros i l Hi Hnot.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  destruct (Z.eqb (Z.rem (Znth (2 * i) l 0) 2) 1) eqn:Heq.
  - apply Z.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

Lemma Nat_even_odd_Z_even_odd_121 : forall n,
  Nat.even n = Z.even (Z.of_nat n) /\
  Nat.odd n = Z.odd (Z.of_nat n).
Proof.
  induction n.
  - simpl. split; reflexivity.
  - destruct IHn as [Heven Hodd].
    rewrite Nat.even_succ, Nat.odd_succ.
    rewrite Nat2Z.inj_succ.
    rewrite Z.even_succ, Z.odd_succ.
    split.
    + exact Hodd.
    + exact Heven.
Qed.

Lemma Nat_odd_Z_odd_121 : forall n,
  Nat.odd n = Z.odd (Z.of_nat n).
Proof.
  intro n.
  apply Nat_even_odd_Z_even_odd_121.
Qed.

Lemma Nat_odd_Z_to_nat_rem_121 : forall x,
  Nat.odd (Z.to_nat x) = Z.eqb (Z.rem x 2) 1.
Proof.
  intros x.
  destruct (Z_lt_le_dec x 0) as [Hneg | Hnonneg].
  - assert (Z.to_nat x = O) as Hto_nat.
    { destruct x; reflexivity || lia. }
    rewrite Hto_nat.
    simpl.
    symmetry.
    apply Z.eqb_neq.
    intro Hrem.
    pose proof (Z.rem_sign_mul x 2 ltac:(lia)) as Hsign.
    rewrite Hrem in Hsign.
    lia.
  - rewrite Nat_odd_Z_odd_121.
    rewrite Z2Nat.id by lia.
    rewrite Z.rem_mod_nonneg by lia.
    rewrite Zmod_odd.
    destruct (Z.odd x); reflexivity.
Qed.

Lemma odd_even_position_add_z_nonneg_121 : forall x,
  0 <= odd_even_position_add_z x.
Proof.
  intros x.
  unfold odd_even_position_add_z.
  destruct (Z.eqb (Z.rem x 2) 1) eqn:Hrem; [|lia].
  apply Z.eqb_eq in Hrem.
  pose proof (Z.rem_sign_mul x 2 ltac:(lia)) as Hsign.
  rewrite Hrem in Hsign.
  lia.
Qed.

Lemma odd_even_position_add_z_to_nat_121 : forall x,
  odd_even_position_add_z x =
  Z.of_nat (if Nat.odd (Z.to_nat x) then Z.to_nat x else O).
Proof.
  intros x.
  unfold odd_even_position_add_z.
  rewrite Nat_odd_Z_to_nat_rem_121.
  destruct (Z.eqb (Z.rem x 2) 1) eqn:Hrem; [|reflexivity].
  apply Z.eqb_eq in Hrem.
  symmetry. apply Z2Nat.id.
  pose proof (Z.rem_sign_mul x 2 ltac:(lia)) as Hsign.
  rewrite Hrem in Hsign.
  lia.
Qed.

Lemma sum_odd_in_even_positions_z_nonneg_121 : forall l,
  0 <= sum_odd_in_even_positions_z l.
Proof.
  fix IH 1.
  intros [|x [|y rest]]; simpl.
  - lia.
  - apply odd_even_position_add_z_nonneg_121.
  - pose proof (odd_even_position_add_z_nonneg_121 x).
    pose proof (IH rest).
    lia.
Qed.

Lemma sum_odd_in_even_positions_z_to_nat_121 : forall l,
  sum_odd_in_even_positions_z l =
  Z.of_nat (sum_odd_in_even_positions_nat (map Z.to_nat l)).
Proof.
  fix IH 1.
  intros [|x [|y rest]]; simpl.
  - reflexivity.
  - apply odd_even_position_add_z_to_nat_121.
  - rewrite odd_even_position_add_z_to_nat_121.
    rewrite IH.
    rewrite Nat2Z.inj_add.
    reflexivity.
Qed.

Lemma sum_odd_at_even_upto_nat_cons2_121 : forall n x y rest,
  sum_odd_at_even_upto_nat (S n) (x :: y :: rest) =
  odd_even_position_add_z x + sum_odd_at_even_upto_nat n rest.
Proof.
  induction n; intros x y rest.
  - cbn [sum_odd_at_even_upto_nat].
    unfold odd_even_position_add_z.
    rewrite Znth0_cons.
    destruct (Z.eqb (Z.rem x 2) 1); lia.
  - replace (sum_odd_at_even_upto_nat (S (S n)) (x :: y :: rest))
      with
        (let z := Znth (2 * Z.of_nat (S n)) (x :: y :: rest) 0 in
         if Z.eqb (Z.rem z 2) 1
         then sum_odd_at_even_upto_nat (S n) (x :: y :: rest) + z
         else sum_odd_at_even_upto_nat (S n) (x :: y :: rest)) by reflexivity.
    rewrite IHn.
    replace (Znth (2 * Z.of_nat (S n)) (x :: y :: rest) 0)
      with (Znth (2 * Z.of_nat n) rest 0).
    + cbn [sum_odd_at_even_upto_nat].
      unfold odd_even_position_add_z.
      destruct (Z.eqb (Z.rem x 2) 1);
        destruct (Z.eqb (Z.rem (Znth (2 * Z.of_nat n) rest 0) 2) 1);
        lia.
    + rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      replace (2 * Z.of_nat (S n) - 1 - 1) with (2 * Z.of_nat n) by lia.
      reflexivity.
Qed.

Lemma sum_odd_at_even_upto_nat_complete_121 : forall n l,
  (length l <= 2 * n <= length l + 1)%nat ->
  sum_odd_at_even_upto_nat n l = sum_odd_in_even_positions_z l.
Proof.
  induction n; intros l Hlen.
  - destruct l as [|x rest].
    + reflexivity.
    + simpl in Hlen. lia.
  - destruct l as [|x [|y rest]].
    + simpl in Hlen. exfalso; lia.
    + simpl in Hlen.
      assert (n = O) by lia.
      subst n.
      simpl.
      unfold odd_even_position_add_z.
      rewrite Znth0_cons.
      reflexivity.
    + rewrite sum_odd_at_even_upto_nat_cons2_121.
      simpl in Hlen.
      rewrite IHn by lia.
      reflexivity.
Qed.

Lemma sum_odd_in_even_pos_aux_even_121 : forall l idx,
  Nat.even idx = true ->
  sum_odd_in_even_pos_aux l idx = sum_odd_in_even_positions_nat l.
Proof.
  fix IH 1.
  intros [|x [|y rest]] idx Heven.
  - reflexivity.
  - simpl.
    rewrite Heven.
    rewrite Nat.negb_even.
    destruct (Nat.odd x); simpl; lia.
  - simpl.
    rewrite Heven.
    rewrite Nat.negb_even.
    assert (Hoddidx : Nat.odd idx = false).
    {
      rewrite <- Nat.negb_even.
      rewrite Heven.
      reflexivity.
    }
    replace (match idx with O => false | S n' => Nat.even n' end) with false.
    simpl.
    rewrite IH.
    + reflexivity.
    + rewrite Nat.even_succ_succ.
      exact Heven.
    + destruct idx; simpl in *.
      * reflexivity.
      * rewrite Nat.odd_succ in Hoddidx.
        symmetry. exact Hoddidx.
Qed.

Lemma sum_odd_in_even_pos_impl_pair_121 : forall l,
  sum_odd_in_even_pos_impl l = sum_odd_in_even_positions_nat l.
Proof.
  intro l.
  unfold sum_odd_in_even_pos_impl.
  apply sum_odd_in_even_pos_aux_even_121.
  reflexivity.
Qed.

Lemma problem_121_spec_z_of_exit : forall l i s,
  0 <= i ->
  2 * i <= Zlength l + 1 ->
  Zlength l <= 2 * i ->
  s = sum_odd_at_even_upto i l ->
  problem_121_spec_z l s.
Proof.
  intros l i s Hi Hbound Hexit Hs.
  unfold problem_121_spec_z.
  exists (sum_odd_in_even_pos_impl (map Z.to_nat l)).
  split.
  - subst s.
    unfold sum_odd_at_even_upto.
    rewrite sum_odd_at_even_upto_nat_complete_121.
    + rewrite sum_odd_in_even_positions_z_to_nat_121.
      rewrite sum_odd_in_even_pos_impl_pair_121.
      reflexivity.
    + split.
      * apply Nat2Z.inj_le.
        replace (Z.of_nat (2 * Z.to_nat i)) with (2 * i).
        2:{ rewrite Nat2Z.inj_mul. simpl. rewrite Z2Nat.id by lia. lia. }
        rewrite <- Zlength_correct.
        lia.
      * apply Nat2Z.inj_le.
        replace (Z.of_nat (2 * Z.to_nat i)) with (2 * i).
        2:{ rewrite Nat2Z.inj_mul. simpl. rewrite Z2Nat.id by lia. lia. }
        rewrite Nat2Z.inj_add.
        simpl.
        replace (Z.of_nat (length l)) with (Zlength l) by apply Zlength_correct.
        change (2 * i <= Zlength l + 1).
        lia.
  - unfold problem_121_spec.
    reflexivity.
Qed.
