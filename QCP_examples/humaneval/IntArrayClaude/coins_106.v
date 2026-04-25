Load "../spec/106".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition list_Z_to_nat (l : list Z) : list nat :=
  map Z.to_nat l.

Fixpoint triangular_nat (n : nat) : nat :=
  match n with
  | O => O
  | S k => triangular_nat k + S k
  end.

Definition problem_106_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_106_pre (Z.to_nat n).

Definition problem_106_spec_z (n : Z) (out : list Z) : Prop :=
  0 <= n /\ problem_106_spec (Z.to_nat n) (list_Z_to_nat out).

Definition triangular_z (i : Z) : Z :=
  Z.of_nat (triangular_nat (Z.to_nat i)).

Definition factorial_z (i : Z) : Z :=
  Z.of_nat (fact (Z.to_nat i)).

Definition f_elem (i : Z) : Z :=
  if Z.even i then factorial_z i else triangular_z i.

Definition f_seq (n : Z) : list Z :=
  map (fun i => f_elem (i + 1)) (Zseq 0 (Z.to_nat n)).

Definition f_seq_int_range (n : Z) : Prop :=
  forall i,
    1 <= i <= n ->
    INT_MIN <= i <= INT_MAX /\
    INT_MIN <= triangular_z i <= INT_MAX /\
    INT_MIN <= factorial_z i <= INT_MAX.

Lemma triangular_z_0 :
  triangular_z 0 = 0.
Proof. reflexivity. Qed.

Lemma factorial_z_0 :
  factorial_z 0 = 1.
Proof. reflexivity. Qed.

Lemma triangular_z_step : forall i,
  0 <= i ->
  triangular_z (i + 1) = triangular_z i + (i + 1).
Proof.
  intros i Hi.
  unfold triangular_z.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  rewrite Nat2Z.inj_add.
  rewrite Nat2Z.inj_succ.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma factorial_z_step : forall i,
  0 <= i ->
  factorial_z (i + 1) = factorial_z i * (i + 1).
Proof.
  intros i Hi.
  unfold factorial_z.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  change (Z.of_nat (S (Z.to_nat i) * fact (Z.to_nat i)) =
          Z.of_nat (fact (Z.to_nat i)) * (i + 1)).
  rewrite Nat2Z.inj_mul.
  rewrite Nat2Z.inj_succ.
  rewrite Z2Nat.id by lia.
  ring.
Qed.

Lemma f_seq_Zlength : forall n,
  0 <= n ->
  Zlength (f_seq n) = n.
Proof.
  intros n Hn.
  unfold f_seq.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.

Lemma f_seq_Znth : forall n i,
  0 <= i < n ->
  Znth i (f_seq n) 0 = f_elem (i + 1).
Proof.
  intros n i Hi.
  unfold f_seq.
  unfold Znth.
  eapply nth_error_nth.
  rewrite nth_error_map.
  rewrite nth_error_nth' with (d := 0%Z).
  - rewrite Zseq_nth by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - rewrite Zseq_length.
    lia.
Qed.

Lemma f_seq_sublist_snoc : forall n i,
  0 <= i < n ->
  sublist 0 (i + 1) (f_seq n) =
  sublist 0 i (f_seq n) ++ f_elem (i + 1) :: nil.
Proof.
  intros n i Hi.
  pose proof (f_seq_Zlength n ltac:(lia)) as Hlen.
  assert (Hsplit_lo : 0 <= 0 <= i) by lia.
  assert (Hsplit_hi : i <= i + 1 <= Z.of_nat (length (f_seq n)))
    by (rewrite <- Zlength_correct; rewrite Hlen; lia).
  rewrite (sublist_split 0 (i + 1) i (f_seq n) Hsplit_lo Hsplit_hi).
  rewrite (sublist_single i (f_seq n) 0).
  - rewrite f_seq_Znth by lia.
    reflexivity.
  - rewrite <- Zlength_correct.
    rewrite Hlen.
    lia.
Qed.

Lemma f_elem_even : forall i,
  Z.even i = true ->
  f_elem i = factorial_z i.
Proof.
  intros i Heven.
  unfold f_elem.
  rewrite Heven.
  reflexivity.
Qed.

Lemma f_elem_odd : forall i,
  Z.even i = false ->
  f_elem i = triangular_z i.
Proof.
  intros i Hodd.
  unfold f_elem.
  rewrite Hodd.
  reflexivity.
Qed.

Lemma f_elem_even_rem : forall i,
  Z.rem i 2 = 0 ->
  f_elem i = factorial_z i.
Proof.
  intros i Hrem.
  unfold f_elem.
  rewrite Zeven_rem.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma f_elem_odd_rem : forall i,
  Z.rem i 2 <> 0 ->
  f_elem i = triangular_z i.
Proof.
  intros i Hrem.
  unfold f_elem.
  rewrite Zeven_rem.
  apply Z.eqb_neq in Hrem.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma triangular_nat_double : forall n,
  (2 * triangular_nat n = n * (n + 1))%nat.
Proof.
  induction n; simpl; lia.
Qed.

Lemma triangular_nat_formula : forall n,
  triangular_nat n = (n * (n + 1) / 2)%nat.
Proof.
  intros n.
  apply Nat.div_unique_exact.
  - lia.
  - rewrite <- triangular_nat_double.
    reflexivity.
Qed.

Lemma Z_even_of_nat : forall n,
  Z.even (Z.of_nat n) = Nat.even n.
Proof.
  induction n.
  - reflexivity.
  - rewrite Nat.even_succ.
    rewrite <- Nat.negb_even.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
    rewrite Z.even_add.
    simpl.
    rewrite IHn.
    destruct (Nat.even n); reflexivity.
Qed.

Lemma f_elem_of_nat : forall i,
  Z.to_nat (f_elem (Z.of_nat i)) =
  if even i then fact i else triangular_nat i.
Proof.
  intros i.
  unfold f_elem.
  rewrite Z_even_of_nat.
  destruct (even i) eqn:Heven.
  - unfold factorial_z.
    rewrite Nat2Z.id.
    rewrite Nat2Z.id.
    reflexivity.
  - unfold triangular_z.
    rewrite Nat2Z.id.
    rewrite Nat2Z.id.
    reflexivity.
Qed.

Lemma problem_106_spec_z_f_seq : forall n,
  0 <= n ->
  problem_106_spec_z n (f_seq n).
Proof.
  intros n Hn.
  unfold problem_106_spec_z, problem_106_spec, list_Z_to_nat.
  split; [lia |].
  split.
  - unfold f_seq.
    rewrite length_map, length_map, Zseq_length.
    reflexivity.
  - intros i Hi_lo Hi_hi.
    unfold f_seq.
    rewrite nth_error_map.
    rewrite nth_error_map.
    rewrite nth_error_nth' with (d := 0%Z).
    + rewrite Zseq_nth by lia.
      simpl.
      replace (Z.of_nat (i - 1) + 1)%Z with (Z.of_nat i) by lia.
      rewrite f_elem_of_nat.
      destruct (even i) eqn:Heven; [reflexivity |].
      rewrite triangular_nat_formula.
      reflexivity.
    + rewrite Zseq_length.
      lia.
Qed.
