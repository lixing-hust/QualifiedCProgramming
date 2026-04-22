Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.leetcode.verify_20260415_001635_climb_stairs Require Import climb_stairs_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import climb_stairs.
Local Open Scope sac.

Lemma climb_stairs_nat_step : forall n,
  climb_stairs_nat (S (S n)) = climb_stairs_nat (S n) + climb_stairs_nat n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Fixpoint fib_pair (n : nat) : Z * Z :=
  match n with
  | O => (1, 1)
  | S k =>
      let '(a, b) := fib_pair k in
      (b, a + b)
  end.

Definition fib_fast (n : nat) : Z := fst (fib_pair n).

Lemma fib_pair_spec : forall n,
  fib_pair n = (climb_stairs_nat n, climb_stairs_nat (S n)).
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. simpl. f_equal; lia.
Qed.

Lemma climb_eq_fast : forall n, climb_stairs_nat n = fib_fast n.
Proof.
  intro n.
  unfold fib_fast.
  pose proof (f_equal fst (fib_pair_spec n)) as H.
  simpl in H.
  now symmetry.
Qed.

Lemma climb_stairs_nat_pos : forall n, 1 <= climb_stairs_nat n.
Proof.
  assert (Hpair: forall n,
            1 <= climb_stairs_nat n /\ 1 <= climb_stairs_nat (S n)).
  {
    induction n.
    - simpl. split; lia.
    - destruct IHn as [Hn HSn].
      split.
      + exact HSn.
      + rewrite climb_stairs_nat_step.
        lia.
  }
  intro n.
  destruct (Hpair n) as [Hn _].
  exact Hn.
Qed.

Lemma climb_stairs_nat_mono_step : forall n,
  climb_stairs_nat n <= climb_stairs_nat (S n).
Proof.
  intros n.
  destruct n.
  - simpl. lia.
  - destruct n.
    + simpl. lia.
    + replace (climb_stairs_nat (S (S (S n))))
        with (climb_stairs_nat (S (S n)) + climb_stairs_nat (S n)).
      2:{ rewrite climb_stairs_nat_step. reflexivity. }
      pose proof (climb_stairs_nat_pos (S n)).
      lia.
Qed.

Lemma climb_stairs_nat_le : forall a b,
  (a <= b)%nat -> climb_stairs_nat a <= climb_stairs_nat b.
Proof.
  intros a b Hab.
  induction Hab.
  - lia.
  - eapply Z.le_trans; eauto using climb_stairs_nat_mono_step.
Qed.

Lemma climb44_val : climb_stairs_nat 44%nat = 1134903170.
Proof.
  rewrite climb_eq_fast.
  vm_compute.
  reflexivity.
Qed.

Lemma climb43_val : climb_stairs_nat 43%nat = 701408733.
Proof.
  rewrite climb_eq_fast.
  vm_compute.
  reflexivity.
Qed.

Lemma climb_stairs_z_step : forall i,
  2 <= i ->
  climb_stairs_z i = climb_stairs_z (i - 1) + climb_stairs_z (i - 2).
Proof.
  intros i Hi.
  unfold climb_stairs_z.
  set (k := Z.to_nat (i - 2)).
  assert (Hk: Z.to_nat (i - 2) = k) by reflexivity.
  assert (Hi_eq: Z.to_nat i = (k + 2)%nat).
  {
    replace i with ((i - 2) + 2) by lia.
    rewrite Z2Nat.inj_add by lia.
    rewrite Hk.
    reflexivity.
  }
  assert (Hi1_eq: Z.to_nat (i - 1) = (k + 1)%nat).
  {
    replace (i - 1) with ((i - 2) + 1) by lia.
    rewrite Z2Nat.inj_add by lia.
    rewrite Hk.
    reflexivity.
  }
  rewrite Hi_eq, Hi1_eq.
  replace (k + 2)%nat with (S (S k)) by lia.
  replace (k + 1)%nat with (S k) by lia.
  rewrite climb_stairs_nat_step.
  reflexivity.
Qed.

Lemma proof_of_climbStairs_entail_wit_1 : climbStairs_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_climbStairs_entail_wit_2 : climbStairs_entail_wit_2.
Proof.
  unfold climbStairs_entail_wit_2.
  intros.
  Intros.
  replace ((i + 1) - 2) with (i - 1) by lia.
  replace ((i + 1) - 1) with i by lia.
  entailer!.
  rewrite climb_stairs_z_step by lia.
  lia.
Qed.

Lemma proof_of_climbStairs_return_wit_1 : climbStairs_return_wit_1.
Proof.
  unfold climbStairs_return_wit_1.
  intros.
  Intros.
  entailer!.
  assert (Hcase: n_pre = 0 \/ n_pre = 1) by lia.
  destruct Hcase as [Hz | Hz]; subst n_pre; unfold climb_stairs_z; reflexivity.
Qed.

Lemma proof_of_climbStairs_safety_wit_7 : climbStairs_safety_wit_7.
Proof.
  unfold climbStairs_safety_wit_7.
  intros.
  Intros.
  subst.
  entailer!.
  - unfold climb_stairs_z.
    pose proof (climb_stairs_nat_pos (Z.to_nat (i - 1))).
    pose proof (climb_stairs_nat_pos (Z.to_nat (i - 2))).
    lia.
  - unfold climb_stairs_z.
    assert (Hto1: (Z.to_nat (i - 1) <= Z.to_nat 44)%nat).
    {
      assert (Hconv1: i - 1 <= 44 <-> (Z.to_nat (i - 1) <= Z.to_nat 44)%nat).
      {
        apply Z2Nat.inj_le; lia.
      }
      apply (proj1 Hconv1); lia.
    }
    assert (Hto2: (Z.to_nat (i - 2) <= Z.to_nat 43)%nat).
    {
      assert (Hconv2: i - 2 <= 43 <-> (Z.to_nat (i - 2) <= Z.to_nat 43)%nat).
      {
        apply Z2Nat.inj_le; lia.
      }
      apply (proj1 Hconv2); lia.
    }
    replace (Z.to_nat 44) with 44%nat in Hto1 by reflexivity.
    replace (Z.to_nat 43) with 43%nat in Hto2 by reflexivity.
    eapply Z.le_trans.
    + apply Z.add_le_mono.
      * apply climb_stairs_nat_le. exact Hto1.
      * apply climb_stairs_nat_le. exact Hto2.
    + rewrite climb44_val, climb43_val. lia.
Qed.
