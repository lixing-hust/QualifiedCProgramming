Load "../spec/139".
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Fixpoint factorial_nat_z (n : nat) : Z :=
  match n with
  | O => 1
  | S k => Z.of_nat (S k) * factorial_nat_z k
  end.

Fixpoint bfact_nat_z (n : nat) : Z :=
  match n with
  | O => 1
  | S k => bfact_nat_z k * factorial_nat_z (S k)
  end.

Definition factorial (n : Z) : Z := factorial_nat_z (Z.to_nat n).
Definition bfact_coq (n : Z) : Z := bfact_nat_z (Z.to_nat n).

Definition problem_139_pre_z (n : Z) : Prop := problem_139_pre (Z.to_nat n).
Definition problem_139_spec_z (n r : Z) : Prop := r = bfact_coq n.

Lemma factorial_0 : factorial 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma bfact_coq_0 : bfact_coq 0 = 1.
Proof.
  reflexivity.
Qed.

Lemma factorial_step :
  forall i,
    1 <= i ->
    factorial (i - 1) * i = factorial i.
Proof.
  intros i Hi.
  unfold factorial.
  destruct (Z.to_nat i) as [|k] eqn:Hni; [lia|].
  rewrite Z2Nat.inj_sub by lia.
  rewrite Hni.
  simpl.
  assert (Hi_eq : i = Z.of_nat (S k)).
  {
    rewrite <- (Z2Nat.id i) at 1 by lia.
    rewrite Hni.
    reflexivity.
  }
  rewrite Hi_eq.
  rewrite Nat.sub_0_r.
  rewrite Z.mul_comm.
  reflexivity.
Qed.

Lemma bfact_coq_step :
  forall i,
    1 <= i ->
    bfact_coq (i - 1) * factorial i = bfact_coq i.
Proof.
  intros i Hi.
  unfold bfact_coq, factorial.
  destruct (Z.to_nat i) as [|k] eqn:Hni; [lia|].
  rewrite Z2Nat.inj_sub by lia.
  rewrite Hni.
  simpl.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.
