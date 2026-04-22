Load "../spec/46".

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition fib4_z (n : Z) : Z :=
  Z.of_nat (fib4 (Z.to_nat n)).

Definition problem_46_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_46_pre (Z.to_nat n).

Definition problem_46_spec_z (n output : Z) : Prop :=
  0 <= n /\ output = fib4_z n.

Lemma fib4_z_0 :
  fib4_z 0 = 0.
Proof. reflexivity. Qed.

Lemma fib4_z_1 :
  fib4_z 1 = 0.
Proof. reflexivity. Qed.

Lemma fib4_z_2 :
  fib4_z 2 = 2.
Proof. reflexivity. Qed.

Lemma fib4_z_3 :
  fib4_z 3 = 0.
Proof. reflexivity. Qed.

Lemma fib4_z_step : forall i,
  4 <= i ->
  fib4_z i =
    fib4_z (i - 1) + fib4_z (i - 2) +
    fib4_z (i - 3) + fib4_z (i - 4).
Proof.
  intros i Hi.
  unfold fib4_z.
  assert (Hi0: Z.to_nat i = S (S (S (S (Z.to_nat (i - 4)))))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi1: Z.to_nat (i - 1) = S (S (S (Z.to_nat (i - 4))))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi2: Z.to_nat (i - 2) = S (S (Z.to_nat (i - 4)))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi3: Z.to_nat (i - 3) = S (Z.to_nat (i - 4))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  rewrite Hi0, Hi1, Hi2, Hi3.
  simpl.
  lia.
Qed.

Definition fib4_step_int_range (n : Z) : Prop :=
  forall i,
    4 <= i <= n ->
    INT_MIN <= fib4_z (i - 4) + fib4_z (i - 3) <= INT_MAX /\
    INT_MIN <= fib4_z (i - 4) + fib4_z (i - 3) + fib4_z (i - 2) <= INT_MAX /\
    INT_MIN <= fib4_z (i - 4) + fib4_z (i - 3) + fib4_z (i - 2) + fib4_z (i - 1) <= INT_MAX.

Lemma problem_46_spec_z_base_0 :
  problem_46_spec_z 0 0.
Proof.
  unfold problem_46_spec_z.
  rewrite fib4_z_0.
  lia.
Qed.

Lemma problem_46_spec_z_base_1 :
  problem_46_spec_z 1 0.
Proof.
  unfold problem_46_spec_z.
  rewrite fib4_z_1.
  lia.
Qed.

Lemma problem_46_spec_z_base_2 :
  problem_46_spec_z 2 2.
Proof.
  unfold problem_46_spec_z.
  rewrite fib4_z_2.
  lia.
Qed.

Lemma problem_46_spec_z_base_3 :
  problem_46_spec_z 3 0.
Proof.
  unfold problem_46_spec_z.
  rewrite fib4_z_3.
  lia.
Qed.
