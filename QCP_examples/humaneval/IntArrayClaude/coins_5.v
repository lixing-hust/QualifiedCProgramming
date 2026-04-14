Load "../spec/5".

Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition intersperse_len (n : Z) : Z :=
  if Z.eq_dec n 0 then 0 else 2 * n - 1.

Definition int_value_range (x : Z) : Prop :=
  INT_MIN <= x <= INT_MAX.

Fixpoint intersperse_list (input : list Z) (d : Z) : list Z :=
  match input with
  | nil => nil
  | x :: nil => x :: nil
  | x :: xs => x :: d :: intersperse_list xs d
  end.

Lemma intersperse_list_snoc_nonempty : forall l x d,
  l <> nil ->
  intersperse_list (l ++ [x]) d = intersperse_list l d ++ [d; x].
Proof.
  intros l x d Hnonempty.
  destruct l as [| a xs]; [contradiction Hnonempty; reflexivity |].
  clear Hnonempty.
  revert a.
  induction xs as [| b xs IH]; intros a; simpl; auto.
  destruct xs as [| c xs].
  - reflexivity.
  - change (a :: d :: intersperse_list ((b :: c :: xs) ++ [x]) d =
            a :: d :: (intersperse_list (b :: c :: xs) d ++ [d; x])).
    rewrite (IH b). reflexivity.
Qed.

Lemma intersperse_list_sublist_one : forall l d,
  0 < Z.of_nat (length l) ->
  intersperse_list (sublist 0 1 l) d = [Znth 0 l 0].
Proof.
  intros.
  change 1 with (0 + 1).
  rewrite (sublist_single 0 l 0) by lia.
  reflexivity.
Qed.

Lemma intersperse_list_sublist_snoc : forall l i d,
  1 <= i < Z.of_nat (length l) ->
  intersperse_list (sublist 0 (i + 1) l) d =
  intersperse_list (sublist 0 i l) d ++ [d; Znth i l 0].
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single i l 0) by lia.
  apply intersperse_list_snoc_nonempty.
  intro Hempty.
  pose proof (Zlength_sublist 0 i l).
  assert (0 <= 0 <= i /\ i <= Zlength l) by (rewrite Zlength_correct; lia).
  specialize (H0 H1).
  rewrite Hempty in H0.
  rewrite Zlength_correct in H0.
  simpl in H0.
  lia.
Qed.

Lemma intersperse_list_length : forall (l : list Z) d,
  l <> nil ->
  (length (intersperse_list l d) = 2 * length l - 1)%nat.
Proof.
  induction l as [| x xs IH]; intros d Hne.
  - contradiction.
  - destruct xs as [| y ys].
    + simpl. lia.
    + assert (Hne' : y :: ys <> nil) by discriminate.
      specialize (IH d Hne').
      cbn [intersperse_list length] in IH |- *.
      lia.
Qed.

Lemma intersperse_list_nth_even : forall k (l : list Z) d,
  (k < length l)%nat ->
  nth_error (intersperse_list l d) (2 * k)%nat = nth_error l k.
Proof.
  intros k l d Hlen.
  revert k Hlen.
  induction l as [| x xs IH]; intros k Hlen.
  - simpl in Hlen. lia.
  - destruct k as [| k'].
    + destruct xs; reflexivity.
    + destruct xs as [| y ys].
      * simpl in Hlen. lia.
      * replace (2 * S k')%nat with (S (S (2 * k')))%nat by lia.
        change (nth_error (intersperse_list (x :: y :: ys) d) (S (S (2 * k'))) =
                nth_error (x :: y :: ys) (S k'))
          with (nth_error (intersperse_list (y :: ys) d) (2 * k') =
                nth_error (y :: ys) k').
        apply IH.
        simpl in Hlen.
        apply Nat.succ_lt_mono in Hlen.
        exact Hlen.
Qed.

Lemma intersperse_list_nth_odd : forall k (l : list Z) d,
  (k + 1 < length l)%nat ->
  nth_error (intersperse_list l d) (2 * k + 1)%nat = Some d.
Proof.
  intros k l d Hlen.
  revert k Hlen.
  induction l as [| x xs IH]; intros k Hlen.
  - simpl in Hlen. lia.
  - destruct k as [| k'].
    + destruct xs as [| y ys].
      * simpl in Hlen. lia.
      * reflexivity.
    + destruct xs as [| y ys].
      * simpl in Hlen. lia.
      * replace (2 * S k' + 1)%nat with (S (S (2 * k' + 1)))%nat by lia.
        change (nth_error (intersperse_list (x :: y :: ys) d) (S (S (2 * k' + 1))) = Some d)
          with (nth_error (intersperse_list (y :: ys) d) (2 * k' + 1) = Some d).
        apply IH.
        simpl in Hlen.
        apply Nat.succ_lt_mono in Hlen.
        exact Hlen.
Qed.

Lemma problem_5_spec_intersperse_list : forall (l : list Z) d,
  problem_5_spec l (intersperse_list l d) d.
Proof.
  intros l d.
  unfold problem_5_spec.
  split.
  - intros H. subst. reflexivity.
  - intros n Hlen Hge. subst n.
    assert (Hne : l <> nil).
    { intro H. subst. simpl in Hge. lia. }
    split.
    + apply intersperse_list_length. exact Hne.
    + intros i Hi.
      split.
      * intros [k Hk]. subst i.
        assert (Hdiv : ((2 * k) / 2)%nat = k).
        { rewrite Nat.mul_comm. apply Nat.div_mul. lia. }
        rewrite Hdiv.
        apply intersperse_list_nth_even. lia.
      * intros [k Hk]. subst i.
        apply intersperse_list_nth_odd. lia.
Qed.
