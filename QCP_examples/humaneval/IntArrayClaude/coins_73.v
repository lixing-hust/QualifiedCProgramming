Load "../spec/73".

From AUXLib Require Import List_lemma ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition problem_73_pre_z (arr : list Z) : Prop :=
  problem_73_pre arr.

Fixpoint count_half_mismatches_upto_nat (n : nat) (arr : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let i := Z.of_nat n' in
      count_half_mismatches_upto_nat n' arr +
      (if Z.eqb (Znth i arr 0) (Znth (Zlength arr - 1 - i) arr 0)
       then 0
       else 1)
  end.

Definition count_half_mismatches_upto (i : Z) (arr : list Z) : Z :=
  count_half_mismatches_upto_nat (Z.to_nat i) arr.

Definition problem_73_spec_z (arr : list Z) (out : Z) : Prop :=
  problem_73_spec arr out.

Definition smallest_change_int_range (arr : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i < Zlength arr ->
    INT_MIN <= count_half_mismatches_upto i arr <= INT_MAX /\
    INT_MIN <= count_half_mismatches_upto i arr + 1 <= INT_MAX.

Lemma count_half_mismatches_upto_0 : forall arr,
  count_half_mismatches_upto 0 arr = 0.
Proof.
  reflexivity.
Qed.

Lemma count_half_mismatches_upto_step_eq : forall arr i,
  0 <= i ->
  Znth i arr 0 = Znth (Zlength arr - 1 - i) arr 0 ->
  count_half_mismatches_upto (i + 1) arr =
    count_half_mismatches_upto i arr.
Proof.
  intros arr i Hi Heq.
  unfold count_half_mismatches_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite Heq.
  rewrite Z.eqb_refl.
  lia.
Qed.

Lemma count_half_mismatches_upto_step_neq : forall arr i,
  0 <= i ->
  Znth i arr 0 <> Znth (Zlength arr - 1 - i) arr 0 ->
  count_half_mismatches_upto (i + 1) arr =
    count_half_mismatches_upto i arr + 1.
Proof.
  intros arr i Hi Hneq.
  unfold count_half_mismatches_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  destruct (Z.eqb (Znth i arr 0) (Znth (Zlength arr - 1 - i) arr 0)) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - lia.
Qed.

Lemma count_diff_acc_shift : forall l1 l2 acc,
  count_diff l1 l2 acc = acc + count_diff l1 l2 0.
Proof.
  induction l1.
  - intros l2 acc. destruct l2; simpl; lia.
  - intros l2 acc. destruct l2; simpl; try lia.
    destruct (Z.eqb a z) eqn:Heq.
    + apply IHl1.
    + rewrite (IHl1 l2 (Z.succ acc)).
      rewrite (IHl1 l2 1).
      lia.
Qed.

Lemma count_diff_snoc : forall l1 l2 a b,
  length l1 = length l2 ->
  count_diff (l1 ++ [a]) (l2 ++ [b]) 0 =
  count_diff l1 l2 0 + (if Z.eqb a b then 0 else 1).
Proof.
  induction l1.
  - intros l2 a b Hlen. destruct l2; simpl in *.
    + destruct (Z.eqb a b); reflexivity.
    + lia.
  - intros l2 a0 b Hlen. destruct l2; simpl in *; try lia.
    destruct (Z.eqb a z) eqn:Heq.
    + rewrite IHl1 by lia. reflexivity.
    + rewrite (count_diff_acc_shift (l1 ++ [a0]) (l2 ++ [b]) 1).
      rewrite (count_diff_acc_shift l1 l2 1).
      rewrite IHl1 by lia.
      lia.
Qed.

Lemma firstn_succ_snoc : forall {A : Type} n (l : list A) d,
  (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma rev_skipn_succ_snoc : forall n (l : list Z) d,
  (n < length l)%nat ->
  rev (skipn (length l - S n) l) =
  rev (skipn (length l - n) l) ++ [nth (length l - S n) l d].
Proof.
  intros n l d Hn.
  rewrite <- (firstn_rev (S n) l).
  rewrite <- (firstn_rev n l).
  rewrite firstn_succ_snoc with (d := d) by (rewrite length_rev; lia).
  rewrite rev_nth by lia.
  reflexivity.
Qed.

Lemma count_half_mismatches_upto_nat_spec : forall n arr,
  (n <= length arr)%nat ->
  count_half_mismatches_upto_nat n arr =
  count_diff (firstn n arr) (rev (skipn (length arr - n) arr)) 0.
Proof.
  induction n.
  - intros arr Hn. reflexivity.
  - intros arr Hn.
    assert (Hnlt : (n < length arr)%nat) by lia.
    rewrite firstn_succ_snoc with (d := 0) by exact Hnlt.
    rewrite rev_skipn_succ_snoc with (d := 0) by exact Hnlt.
    rewrite count_diff_snoc.
    + simpl.
      rewrite IHn by lia.
      unfold Znth.
      rewrite Nat2Z.id.
      replace (Z.to_nat (Zlength arr - 1 - Z.of_nat n))
        with (length arr - S n)%nat by (rewrite Zlength_correct; lia).
      reflexivity.
    + rewrite length_firstn.
      rewrite length_rev, length_skipn.
      lia.
Qed.

Lemma problem_73_exit_index : forall (arr : list Z) i,
  0 <= i ->
  2 * i <= Zlength arr ->
  i >= Zlength arr - 1 - i ->
  Z.to_nat i = (length arr / 2)%nat.
Proof.
  intros arr i Hi Hlow Hhigh.
  apply Nat2Z.inj.
  rewrite Z2Nat.id by lia.
  rewrite Nat2Z.inj_div.
  change (Z.of_nat 2) with 2.
  rewrite <- Zlength_correct.
  apply Z.div_unique with (r := Zlength arr - 2 * i).
  - left. lia.
  - lia.
Qed.

Lemma problem_73_spec_z_of_exit : forall arr i out,
  0 <= i ->
  2 * i <= Zlength arr ->
  i >= Zlength arr - 1 - i ->
  out = count_half_mismatches_upto i arr ->
  problem_73_spec_z arr out.
Proof.
  intros arr i out Hi Hbound Hexit Hout.
  unfold problem_73_spec_z, problem_73_spec.
  subst out.
  unfold count_half_mismatches_upto, smallest_change_impl.
  pose proof (problem_73_exit_index arr i Hi Hbound Hexit) as Hidx.
  rewrite Hidx.
  apply count_half_mismatches_upto_nat_spec.
  apply Nat.Div0.div_le_upper_bound.
  lia.
Qed.
