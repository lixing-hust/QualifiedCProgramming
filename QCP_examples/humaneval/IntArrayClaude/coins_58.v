Load "../spec/58".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_58_pre_z (l1 l2 : list Z) : Prop :=
  problem_58_pre l1 l2.

Definition problem_58_spec_z (l1 l2 output : list Z) : Prop :=
  problem_58_spec l1 l2 output.

Definition list_contains (x : Z) (l : list Z) : Prop :=
  In x l.

Definition list_not_contains (x : Z) (l : list Z) : Prop :=
  ~ In x l.

Fixpoint common_values_aux (seen rest l2 : list Z) : list Z :=
  match rest with
  | [] => seen
  | x :: xs =>
      if in_dec Z.eq_dec x seen then
        common_values_aux seen xs l2
      else if in_dec Z.eq_dec x l2 then
        common_values_aux (seen ++ [x]) xs l2
      else
        common_values_aux seen xs l2
  end.

Definition common_values (l1 l2 : list Z) : list Z :=
  common_values_aux [] l1 l2.

Definition common_first_loop
  (l1 l2 : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength l1 /\
  output = common_values (sublist 0 i l1) l2.

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

Lemma common_values_aux_app_one : forall xs seen l2 x,
  common_values_aux seen (xs ++ [x]) l2 =
  let seen' := common_values_aux seen xs l2 in
  if in_dec Z.eq_dec x seen' then seen'
  else if in_dec Z.eq_dec x l2 then seen' ++ [x] else seen'.
Proof.
  induction xs as [| y ys IH]; intros seen l2 x; simpl.
  - reflexivity.
  - destruct (in_dec Z.eq_dec y seen) as [Hyseen | Hyseen].
    + apply IH.
    + destruct (in_dec Z.eq_dec y l2); apply IH.
Qed.

Lemma common_values_snoc_seen : forall xs l2 x,
  In x (common_values xs l2) ->
  common_values (xs ++ [x]) l2 = common_values xs l2.
Proof.
  intros xs l2 x Hin.
  unfold common_values in *.
  rewrite common_values_aux_app_one.
  change ((if in_dec Z.eq_dec x (common_values_aux [] xs l2)
           then common_values_aux [] xs l2
           else if in_dec Z.eq_dec x l2
                then common_values_aux [] xs l2 ++ [x]
                else common_values_aux [] xs l2) = common_values_aux [] xs l2).
  destruct (in_dec Z.eq_dec x (common_values_aux [] xs l2)); [reflexivity | contradiction].
Qed.

Lemma common_values_snoc_not_l2 : forall xs l2 x,
  ~ In x l2 ->
  common_values (xs ++ [x]) l2 = common_values xs l2.
Proof.
  intros xs l2 x Hnot.
  unfold common_values in *.
  rewrite common_values_aux_app_one.
  change ((if in_dec Z.eq_dec x (common_values_aux [] xs l2)
           then common_values_aux [] xs l2
           else if in_dec Z.eq_dec x l2
                then common_values_aux [] xs l2 ++ [x]
                else common_values_aux [] xs l2) = common_values_aux [] xs l2).
  destruct (in_dec Z.eq_dec x (common_values_aux [] xs l2)); [reflexivity |].
  destruct (in_dec Z.eq_dec x l2); [contradiction | reflexivity].
Qed.

Lemma common_values_snoc_new : forall xs l2 x,
  ~ In x (common_values xs l2) ->
  In x l2 ->
  common_values (xs ++ [x]) l2 = common_values xs l2 ++ [x].
Proof.
  intros xs l2 x Hnot Hin_l2.
  unfold common_values in *.
  rewrite common_values_aux_app_one.
  change ((if in_dec Z.eq_dec x (common_values_aux [] xs l2)
           then common_values_aux [] xs l2
           else if in_dec Z.eq_dec x l2
                then common_values_aux [] xs l2 ++ [x]
                else common_values_aux [] xs l2) = common_values_aux [] xs l2 ++ [x]).
  destruct (in_dec Z.eq_dec x (common_values_aux [] xs l2)); [contradiction |].
  destruct (in_dec Z.eq_dec x l2); [reflexivity | contradiction].
Qed.

Lemma common_first_loop_add : forall l1 l2 i output x,
  x = Znth i l1 0 ->
  0 <= i < Zlength l1 ->
  list_not_contains x output ->
  list_contains x l2 ->
  common_first_loop l1 l2 i output ->
  common_first_loop l1 l2 (i + 1) (output ++ [x]).
Proof.
  intros l1 l2 i output x Hx Hi Hnot Hin_l2 Hloop.
  unfold common_first_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite common_values_snoc_new.
  - rewrite <- Hout. reflexivity.
  - unfold list_not_contains in Hnot. rewrite <- Hout. exact Hnot.
  - unfold list_contains in Hin_l2. exact Hin_l2.
Qed.

Lemma common_first_loop_skip_seen : forall l1 l2 i output x,
  x = Znth i l1 0 ->
  0 <= i < Zlength l1 ->
  list_contains x output ->
  common_first_loop l1 l2 i output ->
  common_first_loop l1 l2 (i + 1) output.
Proof.
  intros l1 l2 i output x Hx Hi Hin Hloop.
  unfold common_first_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite common_values_snoc_seen.
  - exact Hout.
  - unfold list_contains in Hin. rewrite <- Hout. exact Hin.
Qed.

Lemma common_first_loop_skip_not_l2 : forall l1 l2 i output x,
  x = Znth i l1 0 ->
  0 <= i < Zlength l1 ->
  list_not_contains x l2 ->
  common_first_loop l1 l2 i output ->
  common_first_loop l1 l2 (i + 1) output.
Proof.
  intros l1 l2 i output x Hx Hi Hnot Hloop.
  unfold common_first_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite common_values_snoc_not_l2.
  - exact Hout.
  - unfold list_not_contains in Hnot. exact Hnot.
Qed.

Lemma common_values_aux_In_iff : forall rest seen l2 x,
  (forall y, In y seen -> In y l2) ->
  In x (common_values_aux seen rest l2) <-> In x seen \/ (In x rest /\ In x l2).
Proof.
  induction rest as [| y ys IH]; intros seen l2 x Hseen; simpl.
  - split; intros H.
    + left. exact H.
    + destruct H as [H | [[] _]]; exact H.
  - destruct (in_dec Z.eq_dec y seen) as [Hyseen | Hyseen].
    + rewrite IH by exact Hseen.
      split; intros H.
      * destruct H as [H | [Hrest Hl2]]; auto.
      * destruct H as [H | [[Hxy | Hrest] Hl2]]; subst; auto.
    + destruct (in_dec Z.eq_dec y l2) as [Hyl2 | Hyl2].
      * rewrite IH.
        2: {
          intros z Hz.
          apply in_app_or in Hz.
          destruct Hz as [Hz | [Hz | []]]; subst; auto.
        }
        split; intros H.
        -- destruct H as [H | [Hrest Hl2]].
           ++ apply in_app_or in H.
              destruct H as [H | [H | []]]; subst; auto.
           ++ auto.
        -- destruct H as [H | [[Hxy | Hrest] Hl2]]; subst.
           ++ left. apply in_or_app. left. exact H.
           ++ left. apply in_or_app. right. simpl; auto.
           ++ right. split; assumption.
      * rewrite IH by exact Hseen.
        split; intros H.
        -- destruct H as [H | [Hrest Hl2]]; auto.
        -- destruct H as [H | [[Hxy | Hrest] Hl2]]; subst; auto; contradiction.
Qed.

Lemma common_values_In_iff : forall l1 l2 x,
  In x (common_values l1 l2) <-> In x l1 /\ In x l2.
Proof.
  intros l1 l2 x.
  unfold common_values.
  rewrite common_values_aux_In_iff.
  - split.
    + intros [H | H]; [contradiction | exact H].
    + intros H. right. exact H.
  - intros y Hy. contradiction.
Qed.

Lemma common_values_aux_NoDup : forall rest seen l2,
  NoDup seen ->
  NoDup (common_values_aux seen rest l2).
Proof.
  induction rest as [| y ys IH]; intros seen l2 Hnodup; simpl.
  - exact Hnodup.
  - destruct (in_dec Z.eq_dec y seen) as [Hyseen | Hyseen].
    + apply IH. exact Hnodup.
    + destruct (in_dec Z.eq_dec y l2) as [Hyl2 | Hyl2].
      * apply IH.
        apply NoDup_app.
        repeat split.
        -- exact Hnodup.
        -- constructor; [intro H; inversion H | constructor].
        -- intros z Hz Hz_tail.
           destruct Hz_tail as [Hz_eq | []].
           subst z. contradiction.
      * apply IH. exact Hnodup.
Qed.

Lemma common_values_NoDup : forall l1 l2,
  NoDup (common_values l1 l2).
Proof.
  intros l1 l2.
  unfold common_values.
  apply common_values_aux_NoDup.
  constructor.
Qed.

Lemma common_first_loop_full : forall l1 l2 output,
  common_first_loop l1 l2 (Zlength l1) output ->
  output = common_values l1 l2.
Proof.
  intros l1 l2 output Hloop.
  unfold common_first_loop in Hloop.
  destruct Hloop as [_ Hout].
  rewrite (sublist_self l1 (Zlength l1) eq_refl) in Hout.
  exact Hout.
Qed.

Lemma problem_58_spec_from_sort : forall l1 l2 common_l output,
  common_first_loop l1 l2 (Zlength l1) common_l ->
  sorted_int_list_by 1 output ->
  Permutation common_l output ->
  problem_58_spec_z l1 l2 output.
Proof.
  intros l1 l2 common_l output Hloop Hsorted Hperm.
  unfold problem_58_spec_z, problem_58_spec.
  split.
  - intros z.
    split; intros Hin.
    + rewrite <- (common_values_In_iff l1 l2 z).
      rewrite <- (common_first_loop_full l1 l2 common_l Hloop).
      eapply Permutation_in.
      * apply Permutation_sym. exact Hperm.
      * exact Hin.
    + eapply Permutation_in.
      * exact Hperm.
      * rewrite (common_first_loop_full l1 l2 common_l Hloop).
        rewrite common_values_In_iff.
        exact Hin.
  - split.
    + simpl in Hsorted. exact Hsorted.
    + apply (Permutation_NoDup Hperm).
      rewrite (common_first_loop_full l1 l2 common_l Hloop).
      apply common_values_NoDup.
Qed.
