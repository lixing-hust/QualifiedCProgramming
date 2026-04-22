Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260421_052410_count_digits Require Import count_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_digits.
Local Open Scope sac.

Lemma count_digits_fuel_nonpositive :
  forall fuel n, n <= 0 -> count_digits_fuel n fuel = 0.
Proof.
  induction fuel; intros n Hn; simpl; auto.
  destruct (Z.leb n 0) eqn:Hleb; auto.
  apply Z.leb_gt in Hleb; lia.
Qed.

Lemma quot_10_lt_pos :
  forall n, 0 < n -> 0 <= n ÷ 10 < n.
Proof.
  intros n Hn.
  assert (Hq_nonneg : 0 <= n ÷ 10) by (apply Z.quot_pos; lia).
  assert (Hrem : 0 <= Z.rem n 10 < 10) by (apply Z.rem_bound_pos; lia).
  pose proof (Z.quot_rem n 10 ltac:(lia)) as Hdecomp.
  lia.
Qed.

Lemma count_digits_fuel_stable :
  forall (fuel : nat) (n : Z) (extra : nat),
    0 < n ->
    (Z.to_nat n <= fuel)%nat ->
    count_digits_fuel n (fuel + extra)%nat = count_digits_fuel n fuel.
Proof.
  intros fuel.
  induction fuel; intros n extra Hn Hfuel.
  - lia.
  - simpl.
    destruct (Z.leb n 0) eqn:Hleb.
    { apply Z.leb_le in Hleb; lia. }
    destruct (Z.leb (n ÷ 10) 0) eqn:Hqleb.
    + apply Z.leb_le in Hqleb.
      rewrite count_digits_fuel_nonpositive by lia.
      rewrite count_digits_fuel_nonpositive by lia.
      reflexivity.
    + apply Z.leb_gt in Hqleb.
      f_equal.
      rewrite IHfuel; auto.
      pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
      apply Nat2Z.inj_le.
      rewrite Z2Nat.id by lia.
      apply Nat2Z.inj_le in Hfuel.
      rewrite Nat2Z.inj_succ in Hfuel.
      rewrite Z2Nat.id in Hfuel by lia.
      lia.
Qed.

Lemma count_digits_fuel_stable_ge :
  forall (n : Z) (fuel : nat),
    0 < n ->
    (Z.to_nat n <= fuel)%nat ->
    count_digits_fuel n fuel = count_digits_z n.
Proof.
  intros n fuel Hn Hfuel.
  unfold count_digits_z.
  destruct (n =? 0) eqn:Heq.
  {
    apply Z.eqb_eq in Heq; lia.
  }
  assert (exists extra, fuel = (Z.to_nat n + extra)%nat) as [extra ->].
  {
    exists (fuel - Z.to_nat n)%nat.
    lia.
  }
  rewrite count_digits_fuel_stable; auto.
Qed.

Lemma count_digits_z_step_zero :
  forall n,
    0 < n ->
    n ÷ 10 = 0 ->
    count_digits_z n = 1.
Proof.
  intros n Hn Hq.
  unfold count_digits_z at 1.
  destruct (n =? 0) eqn:Heq.
  {
    apply Z.eqb_eq in Heq; lia.
  }
  assert (Hto : exists k, Z.to_nat n = S k).
  {
    destruct (Z.to_nat n) eqn:Hz; [lia | eauto].
  }
  destruct Hto as [k Hk].
  rewrite Hk. simpl.
  destruct (Z.leb n 0) eqn:Hleb.
  {
    apply Z.leb_le in Hleb; lia.
  }
  rewrite count_digits_fuel_nonpositive by lia.
  lia.
Qed.

Lemma count_digits_z_step_pos :
  forall n,
    0 < n ->
    0 < n ÷ 10 ->
    count_digits_z n = 1 + count_digits_z (n ÷ 10).
Proof.
  intros n Hn Hqpos.
  unfold count_digits_z at 1.
  destruct (n =? 0) eqn:Heq.
  {
    apply Z.eqb_eq in Heq; lia.
  }
  assert (Hto : exists k, Z.to_nat n = S k).
  {
    destruct (Z.to_nat n) eqn:Hz; [lia | eauto].
  }
  destruct Hto as [k Hk].
  rewrite Hk. simpl.
  destruct (Z.leb n 0) eqn:Hleb.
  {
    apply Z.leb_le in Hleb; lia.
  }
  assert (HkZ : Z.of_nat k = n - 1).
  {
    apply (f_equal Z.of_nat) in Hk.
    rewrite Nat2Z.inj_succ in Hk.
    rewrite Z2Nat.id in Hk by lia.
    lia.
  }
  replace (count_digits_fuel (n ÷ 10) k)
    with (count_digits_z (n ÷ 10)).
  - lia.
  - symmetry.
    apply count_digits_fuel_stable_ge; auto.
    pose proof (quot_10_lt_pos n Hn) as [Hq_nonneg Hq_lt].
    apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia.
    rewrite HkZ.
    lia.
Qed.

Lemma proof_of_count_digits_entail_wit_2 : count_digits_entail_wit_2.
Proof.
  unfold count_digits_entail_wit_2.
  pre_process.
  entailer!.
  - intros Hqpos.
    assert (Hsem: cnt + count_digits_z n = count_digits_z n_pre).
    {
      match goal with
      | H: n > 0 -> cnt + count_digits_z n = count_digits_z n_pre |- _ =>
          apply H; lia
      end.
    }
    rewrite <- Hsem.
    rewrite (count_digits_z_step_pos n ltac:(lia) ltac:(lia)).
    lia.
  - intros Hq0.
    assert (Hsem: cnt + count_digits_z n = count_digits_z n_pre).
    {
      match goal with
      | H: n > 0 -> cnt + count_digits_z n = count_digits_z n_pre |- _ =>
          apply H; lia
      end.
    }
    rewrite <- Hsem.
    rewrite (count_digits_z_step_zero n ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (quot_10_lt_pos n ltac:(lia)) as [Hq_nonneg Hq_lt].
    lia.
  - pose proof (quot_10_lt_pos n ltac:(lia)) as [Hq_nonneg Hq_lt].
    lia.
  - pose proof (quot_10_lt_pos n ltac:(lia)) as [Hq_nonneg Hq_lt].
    lia.
Qed. 

Lemma proof_of_count_digits_return_wit_1 : count_digits_return_wit_1.
Proof.
  unfold count_digits_return_wit_1.
  pre_process.
  entailer!.
  subst n_pre.
  unfold count_digits_z.
  reflexivity.
Qed. 
