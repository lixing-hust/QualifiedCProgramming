Load "../spec/34".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_34_pre_z (input : list Z) : Prop :=
  problem_34_pre input.

Definition problem_34_spec_z (input output : list Z) : Prop :=
  problem_34_spec input output.

Definition list_contains (x : Z) (l : list Z) : Prop :=
  In x l.

Definition list_not_contains (x : Z) (l : list Z) : Prop :=
  ~ In x l.

Fixpoint seen_values_aux (seen rest : list Z) : list Z :=
  match rest with
  | [] => seen
  | x :: xs =>
      if in_dec Z.eq_dec x seen
      then seen_values_aux seen xs
      else seen_values_aux (seen ++ [x]) xs
  end.

Definition seen_values (l : list Z) : list Z :=
  seen_values_aux [] l.

Definition unique_first_loop (input : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  output = seen_values (sublist 0 i input).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Lemma Znth_In_range : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma In_Znth_exists : forall (x : Z) l,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.

Lemma sublist_snoc_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite Zlength_correct in Hi.
  pose proof (@sublist_split Z 0 (i + 1) i l ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite Hsplit.
  rewrite (@sublist_single Z i l 0) by lia.
  reflexivity.
Qed.

Lemma seen_values_aux_app_one : forall xs seen x,
  seen_values_aux seen (xs ++ [x]) =
  let seen' := seen_values_aux seen xs in
  if in_dec Z.eq_dec x seen' then seen' else seen' ++ [x].
Proof.
  induction xs as [| y ys IH]; intros seen x; simpl.
  - reflexivity.
  - destruct (in_dec Z.eq_dec y seen); apply IH.
Qed.

Lemma seen_values_snoc_seen : forall xs x,
  In x (seen_values xs) ->
  seen_values (xs ++ [x]) = seen_values xs.
Proof.
  intros xs x Hin.
  unfold seen_values in *.
  rewrite seen_values_aux_app_one.
  change ((if in_dec Z.eq_dec x (seen_values_aux [] xs)
           then seen_values_aux [] xs
           else seen_values_aux [] xs ++ [x]) = seen_values_aux [] xs).
  destruct (in_dec Z.eq_dec x (seen_values_aux [] xs)); [reflexivity | contradiction].
Qed.

Lemma seen_values_snoc_new : forall xs x,
  ~ In x (seen_values xs) ->
  seen_values (xs ++ [x]) = seen_values xs ++ [x].
Proof.
  intros xs x Hnot.
  unfold seen_values in *.
  rewrite seen_values_aux_app_one.
  change ((if in_dec Z.eq_dec x (seen_values_aux [] xs)
           then seen_values_aux [] xs
           else seen_values_aux [] xs ++ [x]) = seen_values_aux [] xs ++ [x]).
  destruct (in_dec Z.eq_dec x (seen_values_aux [] xs)); [contradiction | reflexivity].
Qed.

Lemma unique_first_loop_add : forall input i output x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_not_contains x output ->
  unique_first_loop input i output ->
  unique_first_loop input (i + 1) (output ++ [x]).
Proof.
  intros input i output x Hx Hi Hnot Hloop.
  unfold unique_first_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite seen_values_snoc_new.
  - rewrite <- Hout. reflexivity.
  - unfold list_not_contains in Hnot. rewrite <- Hout. exact Hnot.
Qed.

Lemma unique_first_loop_skip : forall input i output x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_contains x output ->
  unique_first_loop input i output ->
  unique_first_loop input (i + 1) output.
Proof.
  intros input i output x Hx Hi Hin Hloop.
  unfold unique_first_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite seen_values_snoc_seen.
  - exact Hout.
  - unfold list_contains in Hin. rewrite <- Hout. exact Hin.
Qed.

Lemma seen_values_aux_In_iff : forall rest seen x,
  In x (seen_values_aux seen rest) <-> In x seen \/ In x rest.
Proof.
  induction rest as [| y ys IH]; intros seen x; simpl.
  - tauto.
  - destruct (in_dec Z.eq_dec y seen) as [Hy | Hy].
    + rewrite IH. split; intros H.
      * destruct H as [H | H]; auto.
      * destruct H as [H | [H | H]]; subst; auto.
    + rewrite IH. split; intros H.
      * destruct H as [H | H].
        -- apply in_app_or in H. destruct H as [H | [H | []]]; subst; auto.
        -- auto.
      * destruct H as [H | [H | H]]; subst; auto.
        -- left. apply in_or_app. left. exact H.
        -- left. apply in_or_app. right. simpl; auto.
Qed.

Lemma seen_values_In_iff : forall input x,
  In x (seen_values input) <-> In x input.
Proof.
  intros input x.
  unfold seen_values.
  rewrite seen_values_aux_In_iff.
  split.
  - intros [H | H]; [contradiction | exact H].
  - intros H. right. exact H.
Qed.

Lemma seen_values_aux_NoDup_simple : forall rest seen,
  NoDup seen ->
  NoDup (seen_values_aux seen rest).
Proof.
  induction rest as [| y ys IH]; intros seen Hnodup; simpl.
  - exact Hnodup.
  - destruct (in_dec Z.eq_dec y seen) as [Hy | Hy].
    + apply IH. exact Hnodup.
    + apply IH.
      apply NoDup_app.
      repeat split.
      * exact Hnodup.
      * constructor; [intro H; inversion H | constructor].
      * intros z Hz Hz_tail.
        destruct Hz_tail as [Hz_eq | []].
        subst z. contradiction.
Qed.

Lemma seen_values_NoDup : forall input,
  NoDup (seen_values input).
Proof.
  intros input.
  unfold seen_values.
  apply seen_values_aux_NoDup_simple.
  constructor.
Qed.

Lemma unique_first_loop_full : forall input output,
  unique_first_loop input (Zlength input) output ->
  output = seen_values input.
Proof.
  intros input output Hloop.
  unfold unique_first_loop in Hloop.
  destruct Hloop as [_ Hout].
  rewrite (sublist_self input (Zlength input) eq_refl) in Hout.
  exact Hout.
Qed.

Lemma problem_34_spec_from_sort : forall input unique_l output,
  unique_first_loop input (Zlength input) unique_l ->
  sorted_int_list_by 1 output ->
  Permutation unique_l output ->
  problem_34_spec_z input output.
Proof.
  intros input unique_l output Hloop Hsorted Hperm.
  unfold problem_34_spec_z, problem_34_spec.
  split.
  - simpl in Hsorted. exact Hsorted.
  - split.
    + apply (Permutation_NoDup Hperm).
      rewrite (unique_first_loop_full input unique_l Hloop).
      apply seen_values_NoDup.
    + intros z.
      split; intros Hin.
      * eapply Permutation_in.
        -- exact Hperm.
        -- 
        rewrite (unique_first_loop_full input unique_l Hloop).
        rewrite seen_values_In_iff.
        exact Hin.
      * rewrite <- seen_values_In_iff.
        rewrite <- (unique_first_loop_full input unique_l Hloop).
        eapply Permutation_in.
        -- apply Permutation_sym. exact Hperm.
        --
        exact Hin.
Qed.
