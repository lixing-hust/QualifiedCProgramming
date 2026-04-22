Load "../spec/55".

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition fib_seq (n : Z) : Z :=
  Z.of_nat (fib (Z.to_nat n)).

Definition problem_55_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_55_pre (Z.to_nat n).

Definition problem_55_spec_z (n res : Z) : Prop :=
  0 <= n /\ 0 <= res /\ problem_55_spec (Z.to_nat n) (Z.to_nat res).

Lemma fib_seq_0 :
  fib_seq 0 = 0.
Proof. reflexivity. Qed.

Lemma fib_seq_1 :
  fib_seq 1 = 1.
Proof. reflexivity. Qed.

Lemma fib_seq_step : forall i,
  2 <= i ->
  fib_seq i = fib_seq (i - 2) + fib_seq (i - 1).
Proof.
  intros i Hi.
  unfold fib_seq.
  assert (Hi0: Z.to_nat i = S (S (Z.to_nat (i - 2)))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi1: Z.to_nat (i - 1) = S (Z.to_nat (i - 2))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  rewrite Hi0, Hi1.
  simpl.
  lia.
Qed.

Definition fib_step_int_range (n : Z) : Prop :=
  forall i,
    2 <= i <= n ->
    INT_MIN <= fib_seq (i - 2) + fib_seq (i - 1) <= INT_MAX.

Lemma problem_55_spec_z_of_fib_seq : forall n res,
  0 <= n ->
  res = fib_seq n ->
  problem_55_spec_z n res.
Proof.
  intros n res Hn Hres.
  unfold problem_55_spec_z, problem_55_spec, fib_seq in *.
  subst res.
  repeat split; try lia.
Qed.
