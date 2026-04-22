Load "../spec/63".

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition fibfib_z (n : Z) : Z :=
  Z.of_nat (fibfib (Z.to_nat n)).

Definition problem_63_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_63_pre (Z.to_nat n).

Definition problem_63_spec_z (n res : Z) : Prop :=
  0 <= n /\ 0 <= res /\ problem_63_spec (Z.to_nat n) (Z.to_nat res).

Lemma fibfib_z_0 :
  fibfib_z 0 = 0.
Proof. reflexivity. Qed.

Lemma fibfib_z_1 :
  fibfib_z 1 = 0.
Proof. reflexivity. Qed.

Lemma fibfib_z_2 :
  fibfib_z 2 = 1.
Proof. reflexivity. Qed.

Lemma fibfib_z_step : forall i,
  3 <= i ->
  fibfib_z i =
    fibfib_z (i - 1) + fibfib_z (i - 2) + fibfib_z (i - 3).
Proof.
  intros i Hi.
  unfold fibfib_z.
  assert (Hi0: Z.to_nat i = S (S (S (Z.to_nat (i - 3))))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi1: Z.to_nat (i - 1) = S (S (Z.to_nat (i - 3)))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hi2: Z.to_nat (i - 2) = S (Z.to_nat (i - 3))).
  { apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite !Nat2Z.inj_succ.
    rewrite Z2Nat.id by lia.
    lia. }
  rewrite Hi0, Hi1, Hi2.
  simpl.
  lia.
Qed.

Definition fibfib_step_int_range (n : Z) : Prop :=
  forall i,
    3 <= i <= n ->
    INT_MIN <= fibfib_z (i - 3) + fibfib_z (i - 2) <= INT_MAX /\
    INT_MIN <= fibfib_z (i - 3) + fibfib_z (i - 2) + fibfib_z (i - 1) <= INT_MAX.

Lemma problem_63_spec_z_of_fibfib_z : forall n res,
  0 <= n ->
  res = fibfib_z n ->
  problem_63_spec_z n res.
Proof.
  intros n res Hn Hres.
  unfold problem_63_spec_z, problem_63_spec, fibfib_z in *.
  subst res.
  repeat split; try lia.
Qed.

Lemma problem_63_spec_z_base_0 :
  problem_63_spec_z 0 0.
Proof.
  apply problem_63_spec_z_of_fibfib_z.
  - lia.
  - rewrite fibfib_z_0. reflexivity.
Qed.

Lemma problem_63_spec_z_base_1 :
  problem_63_spec_z 1 0.
Proof.
  apply problem_63_spec_z_of_fibfib_z.
  - lia.
  - rewrite fibfib_z_1. reflexivity.
Qed.

Lemma problem_63_spec_z_base_2 :
  problem_63_spec_z 2 1.
Proof.
  apply problem_63_spec_z_of_fibfib_z.
  - lia.
  - rewrite fibfib_z_2. reflexivity.
Qed.
