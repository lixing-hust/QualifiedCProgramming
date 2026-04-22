Load "../spec/26".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition list_contains (x : Z) (l : list Z) : Prop :=
  In x l.

Definition list_not_contains (x : Z) (l : list Z) : Prop :=
  ~ In x l.

Definition appears_twice (x : Z) (l : list Z) : Prop :=
  exists i j,
    i <> j /\
    nth_error l i = Some x /\
    nth_error l j = Some x.

Lemma nth_error_In_Z : forall (x : Z) l,
  In x l ->
  exists i, nth_error l i = Some x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  exact Hin.
Qed.

Lemma nth_error_appears_twice : forall x l i j,
  i <> j ->
  nth_error l i = Some x ->
  nth_error l j = Some x ->
  appears_twice x l.
Proof.
  intros.
  exists i, j.
  repeat split; assumption.
Qed.

Lemma appears_twice_cons_iff : forall x y ys,
  appears_twice x (y :: ys) <->
  appears_twice x ys \/ (x = y /\ In x ys).
Proof.
  intros x y ys.
  split.
  - intros [i [j [Hneq [Hi Hj]]]].
    destruct i as [|i'], j as [|j']; simpl in *.
    + contradiction.
    + inversion Hi; subst.
      right.
      split; [reflexivity |].
      apply nth_error_In with (n := j').
      exact Hj.
    + inversion Hj; subst.
      right.
      split; [reflexivity |].
      apply nth_error_In with (n := i').
      exact Hi.
    + left.
      exists i', j'.
      repeat split; auto.
  - intros [Htwice | [Heq Hin]].
    + destruct Htwice as [i [j [Hneq [Hi Hj]]]].
      exists (S i), (S j).
      repeat split; simpl; auto; lia.
    + subst y.
      destruct (nth_error_In_Z x ys Hin) as [i Hi].
      exists 0%nat, (S i).
      repeat split; simpl; auto.
Qed.

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

Lemma seen_values_aux_correct : forall rest seen x,
  In x (seen_values_aux seen rest) <-> In x seen \/ In x rest.
Proof.
  induction rest as [| y ys IH]; intros seen x; simpl.
  - tauto.
  - destruct (in_dec Z.eq_dec y seen) as [Hy | Hy].
    + rewrite IH.
      split; intros H.
      * destruct H as [H | H]; auto.
      * destruct H as [H | [H | H]]; subst; auto.
    + rewrite IH.
      split; intros H.
      * destruct H as [H | H].
        -- apply in_app_or in H. destruct H as [H | [H | []]]; subst; auto.
        -- auto.
      * destruct H as [H | [H | H]]; subst; auto.
        -- left. apply in_or_app. left. exact H.
        -- left. apply in_or_app. right. simpl. auto.
Qed.

Fixpoint duplicate_values (seen duplicates rest : list Z) : list Z :=
  match rest with
  | [] => duplicates
  | x :: xs =>
      if in_dec Z.eq_dec x duplicates then
        duplicate_values seen duplicates xs
      else if in_dec Z.eq_dec x seen then
        duplicate_values seen (duplicates ++ [x]) xs
      else
        duplicate_values (seen ++ [x]) duplicates xs
  end.

Definition remove_duplicates_first_loop
  (input : list Z) (i : Z) (has1 has2 : list Z) : Prop :=
  0 <= i <= Zlength input /\
  has1 = seen_values (sublist 0 i input) /\
  has2 = duplicate_values [] [] (sublist 0 i input).

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

Lemma duplicate_values_app_one : forall xs seen dup x,
  (forall y, In y dup -> In y seen) ->
  duplicate_values seen dup (xs ++ [x]) =
  let seen' := seen_values_aux seen xs in
  let dup' := duplicate_values seen dup xs in
  if in_dec Z.eq_dec x dup' then dup'
  else if in_dec Z.eq_dec x seen' then dup' ++ [x] else dup'.
Proof.
  induction xs as [| y ys IH]; intros seen dup x Hsub; simpl.
  - reflexivity.
  - destruct (in_dec Z.eq_dec y dup) as [Hydup | Hydup].
    + destruct (in_dec Z.eq_dec y seen) as [_ | Hnot].
      * exact (IH seen dup x Hsub).
      * contradiction (Hnot (Hsub y Hydup)).
    + destruct (in_dec Z.eq_dec y seen) as [Hyseen | Hyseen].
      * exact (IH seen (dup ++ [y]) x
          ltac:(intros z Hz;
                apply in_app_or in Hz;
                destruct Hz as [Hz | [Hz | []]]; subst; auto)).
      * exact (IH (seen ++ [y]) dup x
          ltac:(intros z Hz; apply in_or_app; left; apply Hsub; exact Hz)).
Qed.

Lemma duplicate_values_app_one_initial : forall xs x,
  duplicate_values [] [] (xs ++ [x]) =
  let seen' := seen_values xs in
  let dup' := duplicate_values [] [] xs in
  if in_dec Z.eq_dec x dup' then dup'
  else if in_dec Z.eq_dec x seen' then dup' ++ [x] else dup'.
Proof.
  intros xs x.
  unfold seen_values.
  rewrite duplicate_values_app_one.
  - reflexivity.
  - intros y Hy; contradiction.
Qed.

Lemma duplicate_values_snoc_dup : forall xs x,
  In x (duplicate_values [] [] xs) ->
  duplicate_values [] [] (xs ++ [x]) = duplicate_values [] [] xs.
Proof.
  intros xs x Hin.
  rewrite duplicate_values_app_one_initial.
  change ((if in_dec Z.eq_dec x (duplicate_values [] [] xs)
           then duplicate_values [] [] xs
           else if in_dec Z.eq_dec x (seen_values xs)
                then duplicate_values [] [] xs ++ [x]
                else duplicate_values [] [] xs) = duplicate_values [] [] xs).
  destruct (in_dec Z.eq_dec x (duplicate_values [] [] xs)); [reflexivity | contradiction].
Qed.

Lemma duplicate_values_snoc_seen : forall xs x,
  ~ In x (duplicate_values [] [] xs) ->
  In x (seen_values xs) ->
  duplicate_values [] [] (xs ++ [x]) = duplicate_values [] [] xs ++ [x].
Proof.
  intros xs x Hnot_dup Hin_seen.
  rewrite duplicate_values_app_one_initial.
  change ((if in_dec Z.eq_dec x (duplicate_values [] [] xs)
           then duplicate_values [] [] xs
           else if in_dec Z.eq_dec x (seen_values xs)
                then duplicate_values [] [] xs ++ [x]
                else duplicate_values [] [] xs) = duplicate_values [] [] xs ++ [x]).
  destruct (in_dec Z.eq_dec x (duplicate_values [] [] xs)); [contradiction |].
  destruct (in_dec Z.eq_dec x (seen_values xs)); [reflexivity | contradiction].
Qed.

Lemma duplicate_values_snoc_new : forall xs x,
  ~ In x (duplicate_values [] [] xs) ->
  ~ In x (seen_values xs) ->
  duplicate_values [] [] (xs ++ [x]) = duplicate_values [] [] xs.
Proof.
  intros xs x Hnot_dup Hnot_seen.
  rewrite duplicate_values_app_one_initial.
  change ((if in_dec Z.eq_dec x (duplicate_values [] [] xs)
           then duplicate_values [] [] xs
           else if in_dec Z.eq_dec x (seen_values xs)
                then duplicate_values [] [] xs ++ [x]
                else duplicate_values [] [] xs) = duplicate_values [] [] xs).
  destruct (in_dec Z.eq_dec x (duplicate_values [] [] xs)); [reflexivity |].
  destruct (in_dec Z.eq_dec x (seen_values xs)); [contradiction | reflexivity].
Qed.

Lemma first_loop_add_duplicate : forall input i has1 has2 x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_contains x has1 ->
  list_not_contains x has2 ->
  remove_duplicates_first_loop input i has1 has2 ->
  remove_duplicates_first_loop input (i + 1) has1 (has2 ++ [x]).
Proof.
  intros input i has1 has2 x Hx Hi Hhas1 Hhas2 Hloop.
  unfold remove_duplicates_first_loop in *.
  destruct Hloop as [Hrange [Hseen Hdup]].
  repeat split; try lia.
  - rewrite sublist_snoc_Znth by lia.
    rewrite <- Hx.
    rewrite seen_values_snoc_seen.
    + exact Hseen.
    + unfold list_contains in Hhas1. rewrite <- Hseen. exact Hhas1.
  - rewrite sublist_snoc_Znth by lia.
    rewrite <- Hx.
    rewrite duplicate_values_snoc_seen.
    + rewrite <- Hdup. reflexivity.
    + unfold list_not_contains in Hhas2. rewrite <- Hdup. exact Hhas2.
    + unfold list_contains in Hhas1. rewrite <- Hseen. exact Hhas1.
Qed.

Lemma first_loop_add_seen : forall input i has1 has2 x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_not_contains x has1 ->
  list_not_contains x has2 ->
  remove_duplicates_first_loop input i has1 has2 ->
  remove_duplicates_first_loop input (i + 1) (has1 ++ [x]) has2.
Proof.
  intros input i has1 has2 x Hx Hi Hhas1 Hhas2 Hloop.
  unfold remove_duplicates_first_loop in *.
  destruct Hloop as [Hrange [Hseen Hdup]].
  repeat split; try lia.
  - rewrite sublist_snoc_Znth by lia.
    rewrite <- Hx.
    rewrite seen_values_snoc_new.
    + rewrite <- Hseen. reflexivity.
    + unfold list_not_contains in Hhas1. rewrite <- Hseen. exact Hhas1.
  - rewrite sublist_snoc_Znth by lia.
    rewrite <- Hx.
    rewrite duplicate_values_snoc_new.
    + exact Hdup.
    + unfold list_not_contains in Hhas2. rewrite <- Hdup. exact Hhas2.
    + unfold list_not_contains in Hhas1. rewrite <- Hseen. exact Hhas1.
Qed.

Lemma seen_values_aux_preserves_seen : forall xs seen x,
  In x seen ->
  In x (seen_values_aux seen xs).
Proof.
  induction xs as [| y ys IH]; intros seen x Hin; simpl; auto.
  destruct (in_dec Z.eq_dec y seen).
  - apply IH; exact Hin.
  - apply IH. apply in_or_app. left; exact Hin.
Qed.

Lemma duplicate_values_subset_seen_aux : forall xs seen dup x,
  (forall y, In y dup -> In y seen) ->
  In x (duplicate_values seen dup xs) ->
  In x (seen_values_aux seen xs).
Proof.
  induction xs as [| y ys IH]; intros seen dup x Hsub Hin; simpl in *.
  - apply Hsub; exact Hin.
  - destruct (in_dec Z.eq_dec y dup) as [Hydup | Hydup].
    + destruct (in_dec Z.eq_dec y seen) as [_ | Hnot].
      * apply IH with (dup := dup); auto.
      * contradiction (Hnot (Hsub y Hydup)).
    + destruct (in_dec Z.eq_dec y seen) as [Hyseen | Hyseen].
      * apply IH with (dup := dup ++ [y]).
        -- intros z Hz. apply in_app_or in Hz.
           destruct Hz as [Hz | [Hz | []]]; subst; auto.
        -- exact Hin.
      * apply IH with (dup := dup).
        -- intros z Hz. apply in_or_app. left. apply Hsub; exact Hz.
        -- exact Hin.
Qed.

Lemma duplicate_values_in_seen_values : forall xs x,
  In x (duplicate_values [] [] xs) ->
  In x (seen_values xs).
Proof.
  intros xs x Hin.
  unfold seen_values.
  eapply duplicate_values_subset_seen_aux; eauto.
Qed.

Lemma duplicate_values_correct_aux : forall rest seen dup x,
  (forall y, In y dup -> In y seen) ->
  In x (duplicate_values seen dup rest) <->
  In x dup \/ (In x seen /\ In x rest) \/ appears_twice x rest.
Proof.
  induction rest as [| y ys IH]; intros seen dup x Hsub; simpl.
  - split; intros H.
    + left; exact H.
    + destruct H as [H | [[_ []] | [i [j [_ [Hi _]]]]]]; auto.
      destruct i; discriminate.
  - rewrite appears_twice_cons_iff.
    destruct (in_dec Z.eq_dec y dup) as [Hydup | Hydup].
    + destruct (in_dec Z.eq_dec y seen) as [_ | Hnot].
      * rewrite IH by exact Hsub.
        split; intros H.
        -- destruct H as [H | [[Hseen Hrest] | Htwice]].
           { left; exact H. }
           { right. left. split; [exact Hseen | simpl; auto]. }
           { right. right. left; exact Htwice. }
        -- destruct H as [H | [[Hseen [Hxy | Hrest]] | [Htwice | [Hxy Hin]]]]; subst.
           { left. exact H. }
           { left. exact Hydup. }
           { right. left. split; assumption. }
           { right. right. exact Htwice. }
           { left. exact Hydup. }
      * contradiction (Hnot (Hsub y Hydup)).
    + destruct (in_dec Z.eq_dec y seen) as [Hyseen | Hyseen].
      * rewrite IH.
        2: {
          intros z Hz. apply in_app_or in Hz.
          destruct Hz as [Hz | [Hz | []]]; subst; auto.
        }
        split; intros H.
        -- destruct H as [H | [[Hseen Hrest] | Htwice]].
           ++ apply in_app_or in H.
              destruct H as [H | [H | []]]; subst; auto.
           ++ right. left. split; [exact Hseen | simpl; auto].
           ++ right. right. left; exact Htwice.
        -- destruct H as [H | [[Hseen [Hxy | Hrest]] | [Htwice | [Hxy Hin]]]]; subst.
           ++ left. apply in_or_app. left. exact H.
           ++ left. apply in_or_app. right. simpl; auto.
           ++ right. left. split; [exact Hseen | exact Hrest].
           ++ right. right. exact Htwice.
           ++ left. apply in_or_app. right. simpl; auto.
      * rewrite IH.
        2: {
          intros z Hz. apply in_or_app. left. apply Hsub; exact Hz.
        }
        split; intros H.
        -- destruct H as [H | [[Hseen Hrest] | Htwice]].
           ++ left; exact H.
           ++ apply in_app_or in Hseen.
              destruct Hseen as [Hseen | [Hxy | []]]; subst.
              ** right. left. split; [exact Hseen | simpl; auto].
              ** right. right. right. split; [reflexivity | exact Hrest].
           ++ right. right. left; exact Htwice.
        -- destruct H as [H | [[Hseen [Hxy | Hrest]] | [Htwice | [Hxy Hin]]]]; subst.
           ++ left. exact H.
           ++ contradiction.
           ++ right. left. split; [apply in_or_app; left; exact Hseen | exact Hrest].
           ++ right. right. exact Htwice.
           ++ right. left. split; [apply in_or_app; right; simpl; auto | exact Hin].
Qed.

Lemma duplicate_values_correct : forall xs x,
  In x (duplicate_values [] [] xs) <-> appears_twice x xs.
Proof.
  intros xs x.
  rewrite duplicate_values_correct_aux.
  - split; intros H.
    + destruct H as [[] | [[[] _] | Htwice]]; exact Htwice.
    + right. right. exact H.
  - intros y Hy; contradiction.
Qed.

Lemma first_loop_skip_duplicate : forall input i has1 has2 x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_contains x has2 ->
  remove_duplicates_first_loop input i has1 has2 ->
  remove_duplicates_first_loop input (i + 1) has1 has2.
Proof.
  intros input i has1 has2 x Hx Hi Hhas2 Hloop.
  unfold remove_duplicates_first_loop in *.
  destruct Hloop as [Hrange [Hseen Hdup]].
  repeat split; try lia.
  - rewrite sublist_snoc_Znth by lia.
    rewrite <- Hx.
    rewrite seen_values_snoc_seen.
    + exact Hseen.
    + rewrite Hdup in Hhas2.
      unfold list_contains in Hhas2.
      apply duplicate_values_in_seen_values.
      exact Hhas2.
  - rewrite sublist_snoc_Znth by lia.
    rewrite <- Hx.
    rewrite duplicate_values_snoc_dup.
    + exact Hdup.
    + rewrite Hdup in Hhas2. unfold list_contains in Hhas2. exact Hhas2.
Qed.

Fixpoint filter_not_in (duplicates input : list Z) : list Z :=
  match input with
  | [] => []
  | x :: xs =>
      if in_dec Z.eq_dec x duplicates
      then filter_not_in duplicates xs
      else x :: filter_not_in duplicates xs
  end.

Definition remove_duplicates_second_loop
  (input has2 : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  output = filter_not_in has2 (sublist 0 i input).

Lemma filter_not_in_snoc_keep : forall duplicates xs x,
  list_not_contains x duplicates ->
  filter_not_in duplicates (xs ++ [x]) =
    filter_not_in duplicates xs ++ [x].
Proof.
  induction xs as [| y ys IH]; intros x Hnot; simpl.
  - unfold list_not_contains in Hnot.
    destruct (in_dec Z.eq_dec x duplicates); [contradiction | reflexivity].
  - destruct (in_dec Z.eq_dec y duplicates); [apply IH; exact Hnot |].
    rewrite (IH x Hnot); reflexivity.
Qed.

Lemma filter_not_in_snoc_skip : forall duplicates xs x,
  list_contains x duplicates ->
  filter_not_in duplicates (xs ++ [x]) =
    filter_not_in duplicates xs.
Proof.
  induction xs as [| y ys IH]; intros x Hin; simpl.
  - unfold list_contains in Hin.
    destruct (in_dec Z.eq_dec x duplicates); [reflexivity | contradiction].
  - destruct (in_dec Z.eq_dec y duplicates); [apply IH; exact Hin |].
    rewrite (IH x Hin); reflexivity.
Qed.

Lemma second_loop_add_output : forall input has2 i output x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_not_contains x has2 ->
  remove_duplicates_second_loop input has2 i output ->
  remove_duplicates_second_loop input has2 (i + 1) (output ++ [x]).
Proof.
  intros input has2 i output x Hx Hi Hnot Hloop.
  unfold remove_duplicates_second_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite filter_not_in_snoc_keep by exact Hnot.
  rewrite <- Hout.
  reflexivity.
Qed.

Lemma second_loop_skip_output : forall input has2 i output x,
  x = Znth i input 0 ->
  0 <= i < Zlength input ->
  list_contains x has2 ->
  remove_duplicates_second_loop input has2 i output ->
  remove_duplicates_second_loop input has2 (i + 1) output.
Proof.
  intros input has2 i output x Hx Hi Hin Hloop.
  unfold remove_duplicates_second_loop in *.
  destruct Hloop as [Hrange Hout].
  split; [lia |].
  rewrite sublist_snoc_Znth by lia.
  rewrite <- Hx.
  rewrite filter_not_in_snoc_skip by exact Hin.
  exact Hout.
Qed.

Lemma filter_not_in_In_iff : forall duplicates input x,
  In x (filter_not_in duplicates input) <-> In x input /\ ~ In x duplicates.
Proof.
  induction input as [| y ys IH]; intros x; simpl.
  - tauto.
  - destruct (in_dec Z.eq_dec y duplicates) as [Hy | Hy].
    + rewrite IH. split; intros H.
      * destruct H as [Hin Hnot]. split; [right; exact Hin | exact Hnot].
      * destruct H as [[Hxy | Hin] Hnot]; subst; [contradiction |].
        split; assumption.
    + simpl. rewrite IH. split; intros H.
      * destruct H as [Hxy | [Hin Hnot]]; subst; auto.
      * destruct H as [[Hxy | Hin] Hnot]; subst; auto.
Qed.

Lemma filter_not_in_nth_error_input : forall duplicates input j v,
  nth_error (filter_not_in duplicates input) j = Some v ->
  exists i, nth_error input i = Some v.
Proof.
  intros duplicates input j v Hj.
  apply nth_error_In in Hj.
  rewrite filter_not_in_In_iff in Hj.
  destruct Hj as [Hin _].
  apply In_nth_error in Hin.
  exact Hin.
Qed.

Lemma not_appears_twice_unique : forall input v i,
  nth_error input i = Some v ->
  ~ appears_twice v input ->
  forall k, nth_error input k = Some v -> k = i.
Proof.
  intros input v i Hi Hnot k Hk.
  destruct (Nat.eq_dec k i) as [Heq | Hneq]; auto.
  exfalso.
  apply Hnot.
  exists i, k.
  repeat split; auto.
Qed.

Lemma unique_not_appears_twice : forall input v i,
  nth_error input i = Some v ->
  (forall k, nth_error input k = Some v -> k = i) ->
  ~ appears_twice v input.
Proof.
  intros input v i Hi Huniq [j [k [Hneq [Hj Hk]]]].
  pose proof (Huniq j Hj) as Hj_eq.
  pose proof (Huniq k Hk) as Hk_eq.
  lia.
Qed.

Lemma filter_not_in_order : forall duplicates input j1 j2 v1 v2,
  nth_error (filter_not_in duplicates input) j1 = Some v1 ->
  nth_error (filter_not_in duplicates input) j2 = Some v2 ->
  (j1 < j2)%nat ->
  exists i1 i2,
    nth_error input i1 = Some v1 /\
    nth_error input i2 = Some v2 /\
    (i1 < i2)%nat.
Proof.
  induction input as [| x xs IH]; intros j1 j2 v1 v2 Hj1 Hj2 Hlt; simpl in *.
  - destruct j1; discriminate.
  - destruct (in_dec Z.eq_dec x duplicates) as [Hx | Hx].
    + destruct (IH j1 j2 v1 v2 Hj1 Hj2 Hlt) as [i1 [i2 [Hi1 [Hi2 Hilt]]]].
      exists (S i1), (S i2).
      split; [simpl; exact Hi1 |].
      split; [simpl; exact Hi2 | lia].
    + destruct j1 as [| j1'], j2 as [| j2']; simpl in *.
      * lia.
      * inversion Hj1; subst.
        destruct (filter_not_in_nth_error_input duplicates xs j2' v2 Hj2)
          as [i2 Hi2].
        exists 0%nat, (S i2).
        split; [simpl; reflexivity |].
        split; [simpl; exact Hi2 | lia].
      * lia.
      * destruct (IH j1' j2' v1 v2 Hj1 Hj2 ltac:(lia))
          as [i1 [i2 [Hi1 [Hi2 Hilt]]]].
        exists (S i1), (S i2).
        split; [simpl; exact Hi1 |].
        split; [simpl; exact Hi2 | lia].
Qed.

Lemma problem_26_spec_filter_not_in_duplicate_values : forall input,
  problem_26_spec input (filter_not_in (duplicate_values [] [] input) input).
Proof.
  intros input.
  repeat split.
  - intros j v Hj.
    destruct (filter_not_in_nth_error_input _ _ _ _ Hj) as [i Hi].
    exists i.
    split; [exact Hi |].
    apply not_appears_twice_unique with (i := i); [exact Hi |].
    intros Htwice.
    apply nth_error_In in Hj.
    rewrite filter_not_in_In_iff in Hj.
    destruct Hj as [_ Hnot].
    apply Hnot.
    rewrite duplicate_values_correct.
    exact Htwice.
  - intros i v Hi Huniq.
    rewrite filter_not_in_In_iff.
    split.
    + apply nth_error_In with (n := i). exact Hi.
    + rewrite duplicate_values_correct.
      apply unique_not_appears_twice with (i := i); assumption.
  - intros j1 j2 v1 v2 Hj1 Hj2 Hlt.
    eapply filter_not_in_order; eauto.
Qed.

Lemma problem_26_spec_from_loops : forall input has1 has2 output,
  remove_duplicates_first_loop input (Zlength input) has1 has2 ->
  remove_duplicates_second_loop input has2 (Zlength input) output ->
  problem_26_spec input output.
Proof.
  intros input has1 has2 output Hfirst Hsecond.
  unfold remove_duplicates_first_loop in Hfirst.
  unfold remove_duplicates_second_loop in Hsecond.
  destruct Hfirst as [_ [_ Hhas2]].
  destruct Hsecond as [_ Hout].
  rewrite (sublist_self input (Zlength input) eq_refl) in Hhas2.
  rewrite (sublist_self input (Zlength input) eq_refl) in Hout.
  subst has2 output.
  apply problem_26_spec_filter_not_in_duplicate_values.
Qed.
