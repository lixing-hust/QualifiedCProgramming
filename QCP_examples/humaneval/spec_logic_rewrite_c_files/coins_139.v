Load "../spec/139".

Definition spec_fact_139 := fact.
Definition spec_brazilian_factorial_impl_139 := brazilian_factorial_impl.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition LLONG_MAX_139 : Z := 9223372036854775807.

Definition problem_139_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_139_pre (Z.to_nat n).

Definition problem_139_spec_z (n output : Z) : Prop :=
  0 <= n /\ 0 <= output /\ problem_139_spec (Z.to_nat n) (Z.to_nat output).

Definition factorial_z (i : Z) : Z :=
  Z.of_nat (spec_fact_139 (Z.to_nat i)).

Definition bfact_z (i : Z) : Z :=
  Z.of_nat (spec_brazilian_factorial_impl_139 (Z.to_nat i)).

Definition special_factorial_safe_z (n : Z) : Prop :=
  1 <= n <= 8 /\
  forall i,
    0 <= i <= n ->
    1 <= factorial_z i <= LLONG_MAX_139 /\
    1 <= bfact_z i <= LLONG_MAX_139.

Ltac split_or_cases :=
  repeat match goal with
         | H : _ \/ _ |- _ => destruct H as [H | H]
         end; subst.

Ltac small_int_cases_0_8 i :=
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia;
  split_or_cases.

Ltac small_int_cases_1_8 i :=
  assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8) by lia;
  split_or_cases.

Lemma factorial_z_step_139 : forall i,
  1 <= i <= 8 ->
  factorial_z i = factorial_z (i - 1) * i.
Proof.
  intros i Hi.
  small_int_cases_1_8 i.
  all: unfold factorial_z; vm_compute; reflexivity.
Qed.

Lemma factorial_z_0_139 :
  factorial_z 0 = 1.
Proof.
  unfold factorial_z, spec_fact_139.
  reflexivity.
Qed.

Lemma Zof_nat_fold_right_mul_app_single : forall l x,
  Z.of_nat (fold_right Nat.mul 1%nat (l ++ x :: nil)) =
  Z.of_nat (fold_right Nat.mul 1%nat l) * Z.of_nat x.
Proof.
  induction l as [| a l IH]; intros x; simpl.
  - change (Z.of_nat (x * 1)%nat = 1 * Z.of_nat x).
    rewrite Nat.mul_1_r.
    lia.
  - rewrite Nat2Z.inj_mul.
    rewrite IH.
    nia.
Qed.

Lemma bfact_z_step_nonneg_139 : forall i,
  0 <= i ->
  bfact_z (i + 1) = bfact_z i * factorial_z (i + 1).
Proof.
  intros i Hi.
  unfold bfact_z, spec_brazilian_factorial_impl_139, brazilian_factorial_impl.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_S.
  replace (1 + Z.to_nat i)%nat with (S (Z.to_nat i)) by lia.
  rewrite map_app.
  cbn [map].
  rewrite Zof_nat_fold_right_mul_app_single.
  unfold factorial_z, spec_fact_139.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  reflexivity.
Qed.

Lemma bfact_z_step_139 : forall i,
  1 <= i <= 8 ->
  bfact_z i = bfact_z (i - 1) * factorial_z i.
Proof.
  intros i Hi.
  replace (bfact_z i) with (bfact_z ((i - 1) + 1)) by (f_equal; lia).
  replace (factorial_z i) with (factorial_z ((i - 1) + 1)) by (f_equal; lia).
  apply bfact_z_step_nonneg_139; lia.
Qed.

Lemma bfact_z_0_139 :
  bfact_z 0 = 1.
Proof.
  unfold bfact_z, spec_brazilian_factorial_impl_139, brazilian_factorial_impl.
  reflexivity.
Qed.

Lemma factorial_z_bound_139 : forall n i,
  special_factorial_safe_z n ->
  0 <= i <= n ->
  1 <= factorial_z i <= LLONG_MAX_139.
Proof.
  intros n i [_ Hsafe] Hi.
  pose proof (Hsafe i Hi) as [Hfact _].
  exact Hfact.
Qed.

Lemma bfact_z_bound_139 : forall n i,
  special_factorial_safe_z n ->
  0 <= i <= n ->
  1 <= bfact_z i <= LLONG_MAX_139.
Proof.
  intros n i [_ Hsafe] Hi.
  pose proof (Hsafe i Hi) as [_ Hbfact].
  exact Hbfact.
Qed.

Lemma problem_139_pre_z_pos : forall n,
  problem_139_pre_z n ->
  0 < n.
Proof.
  intros n [_ Hpre].
  unfold problem_139_pre in Hpre.
  lia.
Qed.

Lemma problem_139_spec_z_bfact : forall n,
  special_factorial_safe_z n ->
  problem_139_spec_z n (bfact_z n).
Proof.
  intros n Hsafe.
  destruct Hsafe as [Hrange Hbounds].
  unfold problem_139_spec_z.
  split; [lia |].
  split.
  - pose proof (Hbounds n ltac:(lia)) as [_ Hbfact].
    lia.
  - unfold problem_139_spec, bfact_z, spec_brazilian_factorial_impl_139.
    rewrite Nat2Z.id.
    reflexivity.
Qed.
