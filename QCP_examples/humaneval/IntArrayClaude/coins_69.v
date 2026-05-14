Load "../spec/69".

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition search_int_range_69 (input : list Z) : Prop :=
  forall i, 0 <= i < Zlength input -> 0 < Znth i input 0 < INT_MAX.

Fixpoint seen_values_aux_69 (seen rest : list Z) : list Z :=
  match rest with
  | [] => seen
  | x :: xs =>
      if in_dec Z.eq_dec x seen
      then seen_values_aux_69 seen xs
      else seen_values_aux_69 (seen ++ [x]) xs
  end.

Definition seen_values_69 (l : list Z) : list Z :=
  seen_values_aux_69 [] l.

Definition zcount_69 (x : Z) (l : list Z) : Z :=
  Z.of_nat (count x l).

Definition positive_list_69 (l : list Z) : Prop :=
  forall x, In x l -> 0 < x.

Definition eligible_69 (l : list Z) (x : Z) : Prop :=
  zcount_69 x l >= x.

Definition counts_for_values_69 (vals prefix : list Z) : list Z :=
  map (fun v => zcount_69 v prefix) vals.

Definition prefix_69 (input : list Z) (i : Z) : list Z :=
  sublist 0 i input.

Definition search_prefix_69 (input : list Z) (i : Z) : Z :=
  search_impl (prefix_69 input i).

Fixpoint has_first_69 (fuel : nat) (x : Z) (vals : list Z) : bool :=
  match fuel, vals with
  | O, _ => false
  | S fuel', [] => false
  | S fuel', v :: vs =>
      if Z.eqb x v then true else has_first_69 fuel' x vs
  end.

Fixpoint update_first_count_69
  (fuel : nat) (x : Z) (vals cnts : list Z) : list Z :=
  match fuel, vals, cnts with
  | O, _, _ => cnts
  | S fuel', v :: vs, c :: cs =>
      if Z.eqb x v
      then (c + 1) :: cs
      else c :: update_first_count_69 fuel' x vs cs
  | _, _, _ => cnts
  end.

Definition max_after_seen_69 (prefix : list Z) (x max : Z) : Z :=
  if (zcount_69 x prefix + 1 >=? x) && (x >? max) then x else max.

Definition max_after_inner_69 (prefix : list Z) (j : Z) (x max : Z) (vals : list Z) : Z :=
  if has_first_69 (Z.to_nat j) x vals
  then max_after_seen_69 prefix x max
  else max.

Definition hit_max_69 (vals cnts : list Z) (j max : Z) : Z :=
  if ((Znth j cnts 0 + 1 >=? Znth j vals 0) && (Znth j vals 0 >? max))
  then Znth j vals 0
  else max.

Definition search_outer_state_69
  (input : list Z) (i : Z) (vals cnts : list Z) (max : Z) : Prop :=
  0 <= i <= Zlength input /\
  vals = seen_values_69 (prefix_69 input i) /\
  cnts = counts_for_values_69 vals (prefix_69 input i) /\
  max = search_prefix_69 input i.

Definition search_inner_state_69
  (input : list Z) (i j : Z) (vals cnts : list Z) (has max : Z) : Prop :=
  0 <= i < Zlength input /\
  let prefix := prefix_69 input i in
  let x := Znth i input 0 in
  let base_vals := seen_values_69 prefix in
  let base_cnts := counts_for_values_69 base_vals prefix in
  0 <= j <= Zlength base_vals /\
  vals = base_vals /\
  cnts = update_first_count_69 (Z.to_nat j) x base_vals base_cnts /\
  has = (if has_first_69 (Z.to_nat j) x base_vals then 1 else 0) /\
  max = max_after_inner_69 prefix j x (search_prefix_69 input i) base_vals.

Definition search_inner_to_outer_69
  (input : list Z) (i : Z) (vals cnts : list Z) (has max : Z) : Prop :=
  if Z.eqb has 1
  then search_outer_state_69 input (i + 1) vals cnts max
  else search_inner_state_69 input i (Zlength vals) vals cnts has max.

Definition search_after_val_write_69
  (input : list Z) (i : Z) (vals cnts : list Z) (max x freq_size : Z) : Prop :=
  exists base_vals base_cnts,
    x = Znth i input 0 /\
    freq_size = Zlength base_vals /\
    vals = base_vals ++ [x] /\
    cnts = base_cnts /\
    search_inner_to_outer_69 input i base_vals base_cnts 0 max.

Definition search_outer_add_new_69
  (input : list Z) (i : Z) (vals cnts : list Z) (max x freq_size added : Z) : Prop :=
  x = Znth i input 0 /\
  added = 1 /\
  freq_size = Zlength vals /\
  search_outer_state_69 input (i + 1) vals cnts max.


Lemma search_outer_state_69_init : forall input,
  search_outer_state_69 input 0 [] [] (-1).
Proof.
  intros input.
  unfold search_outer_state_69.
  split.
  - split.
    + lia.
    + rewrite Zlength_correct; lia.
  - unfold seen_values_69, counts_for_values_69, search_prefix_69, prefix_69.
    repeat rewrite sublist_nil by lia.
    simpl.
    repeat split; reflexivity.
Qed.

Lemma search_inner_state_69_init : forall input i vals cnts max,
  search_outer_state_69 input i vals cnts max ->
  0 <= i < Zlength input ->
  search_inner_state_69 input i 0 vals cnts 0 max.
Proof.
  intros input i vals cnts max Houter Hi.
  unfold search_outer_state_69 in Houter.
  unfold search_inner_state_69.
  destruct Houter as (_ & Hvals & Hcnts & Hmax).
  subst vals cnts max.
  split; [lia|].
  repeat split; try reflexivity; try (rewrite Zlength_correct; lia); lia.
Qed.

Lemma sublist_snoc_Znth_69 : forall (l : list Z) i,
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

Lemma count_le_length_69 : forall x l,
  (count x l <= length l)%nat.
Proof.
  intros x l.
  induction l as [|a l IH]; simpl.
  - lia.
  - destruct (Z.eqb x a); lia.
Qed.

Lemma zcount_bound_69 : forall x l,
  0 <= zcount_69 x l <= Zlength l.
Proof.
  intros x l.
  unfold zcount_69.
  rewrite Zlength_correct.
  pose proof (count_le_length_69 x l).
  split; lia.
Qed.

Lemma count_app_69 : forall x l1 l2,
  count x (l1 ++ l2) = (count x l1 + count x l2)%nat.
Proof.
  intros x l1 l2.
  induction l1 as [|a l1 IH]; simpl.
  - reflexivity.
  - destruct (Z.eqb x a); simpl; rewrite IH; lia.
Qed.

Lemma zcount_snoc_eq_69 : forall x l,
  zcount_69 x (l ++ [x]) = zcount_69 x l + 1.
Proof.
  intros x l.
  unfold zcount_69.
  rewrite count_app_69.
  simpl.
  rewrite Z.eqb_refl.
  lia.
Qed.

Lemma zcount_snoc_neq_69 : forall x y l,
  y <> x ->
  zcount_69 y (l ++ [x]) = zcount_69 y l.
Proof.
  intros x y l Hneq.
  unfold zcount_69.
  rewrite count_app_69.
  simpl.
  destruct (Z.eqb y x) eqn:Heq.
  - apply Z.eqb_eq in Heq; contradiction.
  - lia.
Qed.

Lemma search_impl_find_69 : forall l,
  search_impl l = find_max_satisfying l l (-1).
Proof.
  intros [|a l].
  - reflexivity.
  - unfold search_impl.
    set (m := find_max_satisfying (a :: l) (a :: l) (-1)).
    destruct (m =? -1) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      unfold m in Heq.
      symmetry.
      exact Heq.
    + reflexivity.
Qed.

Lemma find_max_satisfying_app_one_69 : forall lst candidates x current_max,
  find_max_satisfying lst (candidates ++ [x]) current_max =
  let old := find_max_satisfying lst candidates current_max in
  if zcount_69 x lst >=? x then Z.max x old else old.
Proof.
  intros lst candidates x current_max.
  revert current_max.
  induction candidates as [|a candidates IH]; intros current_max; simpl.
  - unfold zcount_69.
    reflexivity.
  - destruct (Z.of_nat (count a lst) >=? a) eqn:Ha; simpl; apply IH.
Qed.

Lemma find_max_satisfying_lower_current_69 : forall lst candidates current_max,
  current_max <= find_max_satisfying lst candidates current_max.
Proof.
  intros lst candidates.
  induction candidates as [|a candidates IH]; intros current_max; simpl.
  - lia.
  - destruct (Z.of_nat (count a lst) >=? a) eqn:Ha.
    + pose proof (IH (Z.max a current_max)).
      lia.
    + apply IH.
Qed.

Lemma find_max_satisfying_lower_candidate_69 : forall lst candidates current_max x,
  In x candidates ->
  eligible_69 lst x ->
  x <= find_max_satisfying lst candidates current_max.
Proof.
  intros lst candidates.
  induction candidates as [|a candidates IH]; intros current_max x Hin Helig; simpl in *.
  - contradiction.
  - destruct Hin as [Hx | Hin].
    + subst a.
      unfold eligible_69, zcount_69 in Helig.
      assert ((Z.of_nat (count x lst) >=? x) = true) as Hge by (apply Z.geb_le; lia).
      rewrite Hge.
      pose proof (find_max_satisfying_lower_current_69 lst candidates (Z.max x current_max)).
      lia.
    + destruct (Z.of_nat (count a lst) >=? a).
      * eapply IH; eauto.
      * eapply IH; eauto.
Qed.

Lemma find_max_satisfying_upper_69 : forall lst candidates current_max bound,
  current_max <= bound ->
  (forall x, In x candidates -> eligible_69 lst x -> x <= bound) ->
  find_max_satisfying lst candidates current_max <= bound.
Proof.
  intros lst candidates.
  induction candidates as [|a candidates IH]; intros current_max bound Hcur Hall; simpl.
  - lia.
  - destruct (Z.of_nat (count a lst) >=? a) eqn:Ha.
    + apply IH.
      * assert (Ha_prop: eligible_69 lst a).
        { unfold eligible_69, zcount_69. apply Z.geb_le in Ha. lia. }
        pose proof (Hall a ltac:(left; reflexivity) Ha_prop).
        lia.
      * intros x Hin Helig.
        apply Hall; auto.
        right; exact Hin.
    + apply IH; auto.
      intros x Hin Helig.
      apply Hall; auto.
      right; exact Hin.
Qed.

Lemma find_max_satisfying_old_le_new_snoc_69 : forall prefix x,
  find_max_satisfying prefix prefix (-1) <=
  find_max_satisfying (prefix ++ [x]) (prefix ++ [x]) (-1).
Proof.
  intros prefix x.
  apply find_max_satisfying_upper_69.
  - apply find_max_satisfying_lower_current_69.
  - intros y Hy Helig.
    apply find_max_satisfying_lower_candidate_69.
    + apply in_or_app; left; exact Hy.
    + unfold eligible_69 in *.
      destruct (Z.eq_dec y x) as [Heq | Hneq].
      * subst y.
        rewrite zcount_snoc_eq_69.
        lia.
      * rewrite zcount_snoc_neq_69 by congruence.
        exact Helig.
Qed.

Lemma search_impl_snoc_69 : forall prefix x,
  search_impl (prefix ++ [x]) =
  if (zcount_69 x prefix + 1 >=? x)
  then Z.max x (search_impl prefix)
  else search_impl prefix.
Proof.
  intros prefix x.
  rewrite !search_impl_find_69.
  rewrite find_max_satisfying_app_one_69.
  rewrite zcount_snoc_eq_69.
  pose proof (find_max_satisfying_lower_current_69 prefix prefix (-1)) as Holdcur.
  pose proof (find_max_satisfying_lower_current_69 (prefix ++ [x]) prefix (-1)) as Hnewcur.
  destruct (zcount_69 x prefix + 1 >=? x) eqn:Hqual.
  - apply Z.le_antisymm.
    + apply Z.max_lub.
      * apply Z.le_max_l.
      * apply find_max_satisfying_upper_69.
        -- eapply Z.le_trans.
           ++ exact Holdcur.
           ++ apply Z.le_max_r.
        -- intros y Hy Helig.
           destruct (Z.eq_dec y x) as [Heq | Hneq].
           ++ subst y; apply Z.le_max_l.
           ++ unfold eligible_69 in Helig.
              rewrite zcount_snoc_neq_69 in Helig by congruence.
              pose proof (find_max_satisfying_lower_candidate_69
                prefix prefix (-1) y Hy Helig).
              lia.
    + apply Z.max_lub.
      * apply Z.le_max_l.
      * apply find_max_satisfying_upper_69.
        -- eapply Z.le_trans.
           ++ exact Hnewcur.
           ++ apply Z.le_max_r.
        -- intros y Hy Helig.
           destruct (Z.eq_dec y x) as [Heq | Hneq].
           ++ subst y; apply Z.le_max_l.
           ++ assert (Hnew: eligible_69 (prefix ++ [x]) y).
              { unfold eligible_69 in *.
                rewrite zcount_snoc_neq_69 by congruence.
                exact Helig. }
              pose proof (find_max_satisfying_lower_candidate_69
                (prefix ++ [x]) prefix (-1) y Hy Hnew).
              eapply Z.le_trans; [eassumption | apply Z.le_max_r].
  - apply Z.le_antisymm.
    + apply find_max_satisfying_upper_69.
      * apply find_max_satisfying_lower_current_69.
      * intros y Hy Helig.
        destruct (Z.eq_dec y x) as [Heq | Hneq].
        -- subst y.
           unfold eligible_69 in Helig.
           rewrite zcount_snoc_eq_69 in Helig.
           assert ((zcount_69 x prefix + 1 >=? x) = true) by (apply Z.geb_le; lia).
           congruence.
        -- unfold eligible_69 in Helig.
           rewrite zcount_snoc_neq_69 in Helig by congruence.
           apply find_max_satisfying_lower_candidate_69; auto.
    + apply find_max_satisfying_upper_69.
      * apply find_max_satisfying_lower_current_69.
      * intros y Hy Helig.
        destruct (Z.eq_dec y x) as [Heq | Hneq].
        -- subst y.
           unfold eligible_69 in Helig.
           assert ((zcount_69 x prefix + 1 >=? x) = true) by (apply Z.geb_le; lia).
           congruence.
        -- assert (Hnew: eligible_69 (prefix ++ [x]) y).
           { unfold eligible_69 in *.
             rewrite zcount_snoc_neq_69 by congruence.
             exact Helig. }
           apply find_max_satisfying_lower_candidate_69; auto.
Qed.

Lemma In_Znth_exists_69 : forall (x : Z) l,
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

Lemma positive_prefix_69 : forall input i,
  search_int_range_69 input ->
  0 <= i <= Zlength input ->
  positive_list_69 (prefix_69 input i).
Proof.
  intros input i Hrange Hi x Hin.
  destruct (In_Znth_exists_69 x (prefix_69 input i) Hin) as (k & Hk & Hx).
  unfold prefix_69 in *.
  assert (Hplen: Zlength (sublist 0 i input) = i).
  { apply Zlength_sublist0; lia. }
  rewrite Hplen in Hk.
  rewrite Znth_sublist0 in Hx by lia.
  subst x.
  apply Hrange.
  lia.
Qed.

Lemma seen_values_aux_correct_69 : forall rest seen x,
  In x (seen_values_aux_69 seen rest) <-> In x seen \/ In x rest.
Proof.
  induction rest as [|y ys IH]; intros seen x; simpl.
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

Lemma seen_values_correct_69 : forall l x,
  In x (seen_values_69 l) <-> In x l.
Proof.
  intros l x.
  unfold seen_values_69.
  rewrite seen_values_aux_correct_69.
  simpl.
  tauto.
Qed.

Lemma seen_values_aux_app_one_69 : forall xs seen x,
  seen_values_aux_69 seen (xs ++ [x]) =
  let seen' := seen_values_aux_69 seen xs in
  if in_dec Z.eq_dec x seen' then seen' else seen' ++ [x].
Proof.
  induction xs as [|y ys IH]; intros seen x; simpl.
  - reflexivity.
  - destruct (in_dec Z.eq_dec y seen); apply IH.
Qed.

Lemma seen_values_snoc_new_69 : forall xs x,
  ~ In x (seen_values_69 xs) ->
  seen_values_69 (xs ++ [x]) = seen_values_69 xs ++ [x].
Proof.
  intros xs x Hnot.
  unfold seen_values_69 in *.
  rewrite seen_values_aux_app_one_69.
  change ((if in_dec Z.eq_dec x (seen_values_aux_69 [] xs)
           then seen_values_aux_69 [] xs
           else seen_values_aux_69 [] xs ++ [x]) =
          seen_values_aux_69 [] xs ++ [x]).
  destruct (in_dec Z.eq_dec x (seen_values_aux_69 [] xs)); [contradiction | reflexivity].
Qed.

Lemma seen_values_snoc_seen_69 : forall xs x,
  In x (seen_values_69 xs) ->
  seen_values_69 (xs ++ [x]) = seen_values_69 xs.
Proof.
  intros xs x Hin.
  unfold seen_values_69 in *.
  rewrite seen_values_aux_app_one_69.
  change ((if in_dec Z.eq_dec x (seen_values_aux_69 [] xs)
           then seen_values_aux_69 [] xs
           else seen_values_aux_69 [] xs ++ [x]) =
          seen_values_aux_69 [] xs).
  destruct (in_dec Z.eq_dec x (seen_values_aux_69 [] xs)); [reflexivity | contradiction].
Qed.

Lemma NoDup_snoc_69 : forall (l : list Z) x,
  NoDup l ->
  ~ In x l ->
  NoDup (l ++ [x]).
Proof.
  intros l x Hnd Hnot.
  induction Hnd as [|a l Hnot_a Hnd IH]; simpl.
  - constructor; [tauto | constructor].
  - constructor.
    + intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | [Hin | []]].
      * apply Hnot_a; exact Hin.
      * subst x. apply Hnot. left; reflexivity.
    + apply IH.
      intro Hin.
      apply Hnot.
      right; exact Hin.
Qed.

Lemma seen_values_aux_NoDup_69 : forall rest seen,
  NoDup seen ->
  NoDup (seen_values_aux_69 seen rest).
Proof.
  induction rest as [|x xs IH]; intros seen Hnd; simpl.
  - exact Hnd.
  - destruct (in_dec Z.eq_dec x seen) as [Hin | Hnot].
    + apply IH; exact Hnd.
    + apply IH.
      apply NoDup_snoc_69; auto.
Qed.

Lemma seen_values_NoDup_69 : forall xs,
  NoDup (seen_values_69 xs).
Proof.
  intros xs.
  unfold seen_values_69.
  apply seen_values_aux_NoDup_69.
  constructor.
Qed.

Lemma Znth_In_69 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma zcount_notin_zero_69 : forall x l,
  ~ In x l ->
  zcount_69 x l = 0.
Proof.
  intros x l Hnot.
  induction l as [|a l IH]; simpl in *.
  - reflexivity.
  - unfold zcount_69 in *; simpl.
    destruct (Z.eqb x a) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst.
      exfalso; apply Hnot; left; reflexivity.
    + assert (~ In x l) by auto.
      specialize (IH H).
      unfold zcount_69 in IH.
      lia.
Qed.

Lemma counts_for_values_snoc_new_69 : forall vals prefix x,
  ~ In x vals ->
  vals = seen_values_69 prefix ->
  counts_for_values_69 (vals ++ [x]) (prefix ++ [x]) =
  counts_for_values_69 vals prefix ++ [1].
Proof.
  intros vals prefix x Hnot Hseen.
  unfold counts_for_values_69.
  rewrite map_app.
  simpl.
  f_equal.
  - apply map_ext_in.
    intros v Hv.
    unfold zcount_69.
    rewrite count_app_69.
    simpl.
    destruct (Z.eqb v x) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst; contradiction.
    + lia.
  - assert (~ In x prefix).
    {
      intro Hin.
      apply Hnot.
      rewrite Hseen.
      apply seen_values_correct_69.
      exact Hin.
    }
    pose proof (zcount_notin_zero_69 x prefix H) as Hz.
    simpl.
    f_equal.
    rewrite zcount_snoc_eq_69.
    rewrite Hz.
    lia.
Qed.

Lemma has_first_full_false_notin_69 : forall vals x,
  has_first_69 (length vals) x vals = false ->
  ~ In x vals.
Proof.
  induction vals as [|v vals IH]; intros x Hfirst; simpl in *.
  - tauto.
  - destruct (Z.eqb x v) eqn:Heq.
    + discriminate.
    + apply Z.eqb_neq in Heq.
      intros [Hin | Hin].
      * subst; contradiction.
      * apply IH in Hfirst.
        contradiction.
Qed.

Lemma search_impl_positive_or_minus_69 : forall l,
  positive_list_69 l ->
  search_impl l = -1 \/ 0 < search_impl l.
Proof.
  intros l Hpos.
  rewrite search_impl_find_69.
  assert (Hfind: forall whole candidates cur,
    positive_list_69 candidates ->
    cur = -1 \/ 0 < cur ->
    find_max_satisfying whole candidates cur = -1 \/
    0 < find_max_satisfying whole candidates cur).
  {
    intros whole candidates.
    induction candidates as [|a candidates IH]; intros cur Hcand Hcur; simpl.
    - exact Hcur.
    - destruct (Z.of_nat (count a whole) >=? a) eqn:Ha.
      + apply IH.
        * intros y Hy. apply Hcand. right; exact Hy.
        * right.
          pose proof (Hcand a ltac:(left; reflexivity)).
          destruct Hcur; subst; lia.
      + apply IH.
        * intros y Hy. apply Hcand. right; exact Hy.
        * exact Hcur.
  }
  apply Hfind; auto.
Qed.

Lemma Zlength_map_69 : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_69 : forall {A B : Type} (f : A -> B) (l : list A) i d d',
  0 <= i < Zlength l ->
  Znth i (map f l) d' = f (Znth i l d).
Proof.
  intros A B f l i d d' Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f d)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - rewrite (@map_nth A B f l d (Z.to_nat i)).
    reflexivity.
Qed.

Lemma counts_for_values_69_length : forall vals prefix,
  Zlength (counts_for_values_69 vals prefix) = Zlength vals.
Proof.
  intros.
  unfold counts_for_values_69.
  apply Zlength_map_69.
Qed.

Lemma Znth_counts_for_values_69_bound : forall vals prefix k,
  0 <= k < Zlength vals ->
  0 <= Znth k (counts_for_values_69 vals prefix) 0 <= Zlength prefix.
Proof.
  intros vals prefix k Hk.
  unfold counts_for_values_69.
  rewrite (Znth_map_69 (fun v => zcount_69 v prefix) vals k 0 0) by lia.
  apply zcount_bound_69.
Qed.

Lemma nth_update_first_count_after_fuel_69 : forall fuel x vals cnts k d,
  (fuel <= k)%nat ->
  nth k (update_first_count_69 fuel x vals cnts) d = nth k cnts d.
Proof.
  induction fuel as [|fuel IH]; intros x vals cnts k d Hk.
  - reflexivity.
  - destruct vals as [|v vals]; destruct cnts as [|c cnts]; try reflexivity.
    destruct k as [|k].
    { lia. }
    simpl.
    destruct (Z.eqb x v); auto.
    apply IH.
    lia.
Qed.

Lemma Znth_update_first_count_at_fuel_69 : forall j x vals cnts,
  0 <= j ->
  Znth j (update_first_count_69 (Z.to_nat j) x vals cnts) 0 = Znth j cnts 0.
Proof.
  intros j x vals cnts Hj.
  unfold Znth.
  apply nth_update_first_count_after_fuel_69.
  lia.
Qed.

Lemma update_first_count_69_length : forall fuel x vals cnts,
  Zlength (update_first_count_69 fuel x vals cnts) = Zlength cnts.
Proof.
  induction fuel as [|fuel IH]; intros x vals cnts; simpl.
  - reflexivity.
  - destruct vals as [|v vals]; destruct cnts as [|c cnts]; simpl; try reflexivity.
    destruct (Z.eqb x v); simpl; repeat rewrite Zlength_cons; rewrite ?IH; reflexivity.
Qed.

Lemma replace_Znth_length_69 : forall {A : Type} (l : list A) i x,
  Zlength (replace_Znth i x l) = Zlength l.
Proof.
  intros A l i x.
  unfold replace_Znth.
  repeat rewrite Zlength_correct.
  f_equal.
  revert l.
  generalize (Z.to_nat i) as n.
  induction n; intros [|a l0]; simpl; try reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Lemma Znth_replace_Znth_eq_69 : forall {A : Type} (l : list A) i x d,
  0 <= i < Zlength l ->
  Znth i (replace_Znth i x l) d = x.
Proof.
  intros A l i x d Hi.
  unfold replace_Znth, Znth.
  assert (Hnth: forall n (l0 : list A),
    (n < length l0)%nat ->
    nth n (replace_nth n x l0) d = x).
  {
    induction n as [|n IH]; intros [|a l0] Hn; simpl in *; try lia.
    - reflexivity.
    - apply IH.
      lia.
  }
  apply Hnth.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma Znth_replace_Znth_neq_69 : forall {A : Type} (l : list A) i k x d,
  0 <= i ->
  0 <= k < Zlength l ->
  k <> i ->
  Znth k (replace_Znth i x l) d = Znth k l d.
Proof.
  intros A l i k x d Hi Hk Hneq.
  unfold replace_Znth, Znth.
  assert (Hnth: forall n m (l0 : list A),
    (m < length l0)%nat ->
    m <> n ->
    nth m (replace_nth n x l0) d = nth m l0 d).
  {
    induction n as [|n IH]; intros [|m] [|a l0] Hm Hmn; simpl in *; try lia; try reflexivity.
    apply IH; lia.
  }
  apply Hnth.
  - rewrite Zlength_correct in Hk.
    lia.
  - lia.
Qed.

Lemma NoDup_Znth_eq_69 : forall (vals : list Z) k j d,
  NoDup vals ->
  0 <= k < Zlength vals ->
  0 <= j < Zlength vals ->
  Znth k vals d = Znth j vals d ->
  k = j.
Proof.
  intros vals k j d Hnd Hk Hj Heq.
  assert (Hnat: Z.to_nat k = Z.to_nat j).
  {
    apply (proj1 (NoDup_nth vals d) Hnd); try (rewrite Zlength_correct in *; lia).
    unfold Znth in Heq.
    exact Heq.
  }
  lia.
Qed.

Lemma update_first_count_false_69 : forall fuel x vals cnts,
  has_first_69 fuel x vals = false ->
  update_first_count_69 fuel x vals cnts = cnts.
Proof.
  induction fuel as [|fuel IH]; intros x vals cnts Hfirst; simpl in *.
  - reflexivity.
  - destruct vals as [|v vals]; destruct cnts as [|c cnts]; simpl in *; try reflexivity.
    destruct (Z.eqb x v) eqn:Heq; try discriminate.
    simpl.
    f_equal.
    apply IH.
    exact Hfirst.
Qed.

Lemma counts_for_values_snoc_hit_replace_69 : forall vals prefix j x,
  NoDup vals ->
  vals = seen_values_69 prefix ->
  0 <= j < Zlength vals ->
  Znth j vals 0 = x ->
  replace_Znth j (Znth j (counts_for_values_69 vals prefix) 0 + 1)
    (counts_for_values_69 vals prefix) =
  counts_for_values_69 vals (prefix ++ [x]).
Proof.
  intros vals prefix j x Hnd Hseen Hj Hx.
  apply (proj2 (list_eq_ext 0 _ _)).
  split.
  - rewrite replace_Znth_length_69.
    repeat rewrite counts_for_values_69_length.
    reflexivity.
  - intros k Hk.
    rewrite replace_Znth_length_69, counts_for_values_69_length in Hk.
    destruct (Z.eq_dec k j) as [Heq | Hneq].
    + subst k.
      rewrite Znth_replace_Znth_eq_69 by (rewrite counts_for_values_69_length; lia).
      unfold counts_for_values_69.
      rewrite (Znth_map_69 (fun v => zcount_69 v prefix) vals j 0 0) by lia.
      rewrite (Znth_map_69 (fun v => zcount_69 v (prefix ++ [x])) vals j 0 0) by lia.
      rewrite Hx.
      rewrite zcount_snoc_eq_69.
      reflexivity.
    + rewrite Znth_replace_Znth_neq_69.
      unfold counts_for_values_69.
      rewrite (Znth_map_69 (fun v => zcount_69 v prefix) vals k 0 0) by lia.
      rewrite (Znth_map_69 (fun v => zcount_69 v (prefix ++ [x])) vals k 0 0) by lia.
      rewrite zcount_snoc_neq_69.
      * reflexivity.
      * intro Hsame.
        assert (k = j).
        {
          eapply NoDup_Znth_eq_69 with (d := 0); eauto; lia.
        }
        contradiction.
      * lia.
      * rewrite counts_for_values_69_length.
        lia.
      * congruence.
Qed.

Lemma search_inner_cnt_at_j_bound_69 : forall input i j vals cnts has max,
  search_inner_state_69 input i j vals cnts has max ->
  0 <= j < Zlength cnts ->
  0 <= Znth j cnts 0 <= i.
Proof.
  intros input i j vals cnts has max Hstate Hj.
  unfold search_inner_state_69 in Hstate.
  destruct Hstate as (Hi & Hjbase & Hvals & Hcnts & Hhas & Hmax).
  subst vals cnts.
  rewrite Znth_update_first_count_at_fuel_69 by lia.
  pose proof (Znth_counts_for_values_69_bound
    (seen_values_69 (prefix_69 input i)) (prefix_69 input i) j) as Hbound.
  rewrite update_first_count_69_length in Hj.
  rewrite counts_for_values_69_length in Hj.
  specialize (Hbound Hj).
  assert (Hplen: Zlength (prefix_69 input i) = i).
  {
    unfold prefix_69.
    rewrite Zlength_sublist by lia.
    lia.
  }
  rewrite Hplen in Hbound.
  lia.
Qed.

Lemma has_first_S_false_69 : forall n x vals d,
  (n < length vals)%nat ->
  has_first_69 n x vals = false ->
  x <> nth n vals d ->
  has_first_69 (S n) x vals = false.
Proof.
  induction n as [|n IH]; intros x [|v vals] d Hlen Hhas Hmiss; simpl in *; try lia.
  - destruct (Z.eqb x v) eqn:Heq; auto.
    apply Z.eqb_eq in Heq.
    contradiction.
  - destruct (Z.eqb x v) eqn:Heq; try discriminate.
    eapply IH with (d := d); auto.
    lia.
Qed.

Lemma update_first_count_S_miss_69 : forall n x vals cnts d,
  (n < length vals)%nat ->
  has_first_69 n x vals = false ->
  x <> nth n vals d ->
  update_first_count_69 (S n) x vals cnts =
  update_first_count_69 n x vals cnts.
Proof.
  induction n as [|n IH]; intros x [|v vals] [|c cnts] d Hlen Hhas Hmiss;
    simpl in *; try lia; try reflexivity.
  - destruct (Z.eqb x v) eqn:Heq; auto.
    apply Z.eqb_eq in Heq.
    contradiction.
  - destruct (Z.eqb x v) eqn:Heq; try discriminate.
    simpl.
    f_equal.
    eapply IH with (d := d); auto.
    lia.
Qed.

Lemma search_inner_state_miss_step_69 : forall input i j vals cnts max,
  search_inner_state_69 input i j vals cnts 0 max ->
  0 <= j < Zlength vals ->
  Znth i input 0 <> Znth j vals 0 ->
  search_inner_state_69 input i (j + 1) vals cnts 0 max.
Proof.
  intros input i j vals cnts max Hstate Hj Hneq.
  unfold search_inner_state_69 in *.
  destruct Hstate as (Hi & Hjbase & Hvals & Hcnts & Hhas & Hmax).
  subst vals cnts.
  set (prefix := prefix_69 input i) in *.
  set (x := Znth i input 0) in *.
  set (base_vals := seen_values_69 prefix) in *.
  set (base_cnts := counts_for_values_69 base_vals prefix) in *.
  assert (Hfirst: has_first_69 (Z.to_nat j) x base_vals = false).
  {
    destruct (has_first_69 (Z.to_nat j) x base_vals); lia.
  }
  assert (Hnth_neq: x <> nth (Z.to_nat j) base_vals 0).
  {
    unfold Znth in Hneq.
    exact Hneq.
  }
  assert (Hlen_nat: (Z.to_nat j < length base_vals)%nat).
  {
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hfirst_next:
    has_first_69 (Z.to_nat (j + 1)) x base_vals = false).
  {
    replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
    eapply has_first_S_false_69; eauto.
  }
  split; [lia|].
  repeat split.
  - lia.
  - lia.
  - assert (Hznat: Z.to_nat (j + 1) = S (Z.to_nat j)) by lia.
    rewrite Hznat.
    symmetry.
    rewrite update_first_count_S_miss_69 with (d := 0); auto.
  - rewrite Hfirst_next.
    reflexivity.
  - unfold max_after_inner_69 in *.
    rewrite Hfirst_next.
    rewrite Hfirst in Hmax.
    exact Hmax.
Qed.

Lemma search_after_val_write_add_count_69 : forall input i vals cnts max x freq_size final_max,
  search_int_range_69 input ->
  0 <= i < Zlength input ->
  search_after_val_write_69 input i vals cnts max x freq_size ->
  ((x = 1 /\ max = -1 /\ final_max = 1) \/
   (max <> -1 /\ final_max = max) \/
   (x <> 1 /\ max = -1 /\ final_max = max)) ->
  search_outer_add_new_69 input i vals (cnts ++ [1]) final_max
    (Znth i input 0) (freq_size + 1) 1.
Proof.
  intros input i vals cnts max x freq_size final_max Hrange Hi Hafter Hcase.
  unfold search_after_val_write_69 in Hafter.
  destruct Hafter as (base_vals & base_cnts & Hx & Hfreq & Hvals & Hcnts & Hinner).
  subst x vals cnts freq_size.
  unfold search_inner_to_outer_69 in Hinner.
  simpl in Hinner.
  unfold search_inner_state_69 in Hinner.
  destruct Hinner as (Hi2 & Hj & Hbase_vals & Hbase_cnts & Hhas & Hmax).
  set (prefix := prefix_69 input i) in *.
  set (x := Znth i input 0) in *.
  subst base_vals.
  assert (Hfirst: has_first_69 (Z.to_nat (Zlength (seen_values_69 prefix))) x
             (seen_values_69 prefix) = false).
  {
    destruct (has_first_69 (Z.to_nat (Zlength (seen_values_69 prefix))) x
      (seen_values_69 prefix)); lia.
  }
  assert (Hfirst_len:
    has_first_69 (length (seen_values_69 prefix)) x (seen_values_69 prefix) = false).
  {
    rewrite <- Hfirst.
    rewrite Zlength_correct.
    rewrite Nat2Z.id.
    reflexivity.
  }
  pose proof (has_first_full_false_notin_69 (seen_values_69 prefix) x Hfirst_len) as Hnot_seen.
  assert (Hnot_prefix: ~ In x prefix).
  {
    intro Hin.
    apply Hnot_seen.
    apply seen_values_correct_69.
    exact Hin.
  }
  assert (Hcnts_base: base_cnts = counts_for_values_69 (seen_values_69 prefix) prefix).
  {
    subst base_cnts.
    assert (Hupdate:
      update_first_count_69 (Z.to_nat (Zlength (seen_values_69 prefix))) x
        (seen_values_69 prefix)
        (counts_for_values_69 (seen_values_69 prefix) prefix) =
      counts_for_values_69 (seen_values_69 prefix) prefix).
    {
      clear -Hfirst_len.
      rewrite Zlength_correct.
      rewrite Nat2Z.id.
      induction (seen_values_69 prefix) as [|v vs IH]; simpl in *; auto.
      destruct (Z.eqb x v) eqn:Heq; try discriminate.
      simpl.
      f_equal.
      apply IH.
      exact Hfirst_len.
    }
    rewrite Hupdate.
    reflexivity.
  }
  subst base_cnts.
  unfold search_outer_add_new_69, search_outer_state_69.
  repeat split; try reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - lia.
  - lia.
  - replace (prefix_69 input (i + 1)) with (prefix ++ [x]).
    symmetry.
    apply seen_values_snoc_new_69.
    exact Hnot_seen.
    unfold prefix_69, prefix, x.
    symmetry.
    apply sublist_snoc_Znth_69; lia.
  - replace (prefix_69 input (i + 1)) with (prefix ++ [x]).
    symmetry.
    rewrite Hcnts_base.
    apply counts_for_values_snoc_new_69; auto.
    unfold prefix_69, prefix, x.
    symmetry.
    apply sublist_snoc_Znth_69; lia.
  - unfold search_prefix_69, prefix_69.
    rewrite sublist_snoc_Znth_69 by lia.
    fold prefix x.
    rewrite search_impl_snoc_69.
    rewrite zcount_notin_zero_69 by exact Hnot_prefix.
    unfold max_after_inner_69 in Hmax.
    rewrite Hfirst in Hmax.
    subst max.
    destruct Hcase as [(Hx1 & Hm & Hfinal) | [(Hmn & Hfinal) | (Hx1 & Hm & Hfinal)]].
    + subst final_max.
      rewrite Hx1.
      unfold search_prefix_69, prefix_69 in Hm.
      fold prefix in Hm.
      rewrite Hm.
      simpl.
      reflexivity.
    + subst final_max.
      destruct (1 >=? x) eqn:Hqualb.
      * assert (Hqual: x <= 1) by (apply Z.geb_le in Hqualb; lia).
        pose proof (positive_prefix_69 input i Hrange ltac:(lia)) as Hpos.
        pose proof (search_impl_positive_or_minus_69 prefix Hpos) as Hres.
        unfold search_prefix_69, prefix_69 in Hmn.
        fold prefix in Hmn.
        destruct Hres as [Hres | Hres]; [contradiction |].
        simpl.
        rewrite Hqualb.
        unfold search_prefix_69, prefix_69.
        change (search_impl (sublist 0 i input)) with (search_impl prefix).
        replace (Z.max x (search_impl prefix)) with (search_impl prefix).
        -- reflexivity.
        -- symmetry.
           apply Z.max_r.
           eapply Z.le_trans.
           ++ exact Hqual.
           ++ lia.
      * simpl.
        rewrite Hqualb.
        unfold search_prefix_69, prefix_69.
        change (search_impl (sublist 0 i input)) with (search_impl prefix).
        reflexivity.
    + subst final_max.
      unfold x in *.
      assert (0 < Znth i input 0) by (apply Hrange; lia).
      assert ((1 >=? x) = false).
      {
        destruct (1 >=? x) eqn:Hge; auto.
        apply Z.geb_le in Hge.
        lia.
      }
      simpl.
      change (0 + 1) with 1.
      destruct (1 >=? Znth i input 0) eqn:Hge.
      {
        apply Z.geb_le in Hge.
        lia.
      }
      reflexivity.
Qed.

Lemma search_hit_to_outer_69 : forall input i j vals cnts has max,
  search_inner_state_69 input i j vals cnts has max ->
  has = 0 ->
  0 <= j < Zlength vals ->
  Znth j vals 0 = Znth i input 0 ->
  search_outer_state_69 input (i + 1) vals
    (replace_Znth j (Znth j cnts 0 + 1) cnts)
    (hit_max_69 vals cnts j max).
Proof.
  intros input i j vals cnts has max Hstate Hhas0 Hj Hhit.
  unfold search_inner_state_69 in Hstate.
  destruct Hstate as (Hi & Hjbase & Hvals & Hcnts & Hhas & Hmax).
  set (prefix := prefix_69 input i) in *.
  set (x := Znth i input 0) in *.
  set (base_vals := seen_values_69 prefix) in *.
  set (base_cnts := counts_for_values_69 base_vals prefix) in *.
  subst vals.
  fold x in Hhit.
  assert (Hfirst_false: has_first_69 (Z.to_nat j) x base_vals = false).
  {
    destruct (has_first_69 (Z.to_nat j) x base_vals); lia.
  }
  assert (Hcnts_base: cnts = base_cnts).
  {
    subst cnts.
    apply update_first_count_false_69.
    exact Hfirst_false.
  }
  subst cnts.
  assert (Hseen_snoc: seen_values_69 (prefix ++ [x]) = base_vals).
  {
    apply seen_values_snoc_seen_69.
    rewrite <- Hhit.
    apply Znth_In_69.
    exact Hj.
  }
  assert (Hmax_base: max = search_prefix_69 input i).
  {
    unfold max_after_inner_69 in Hmax.
    rewrite Hfirst_false in Hmax.
    exact Hmax.
  }
  assert (Hcnt_at: Znth j base_cnts 0 = zcount_69 x prefix).
  {
    unfold base_cnts, counts_for_values_69.
    rewrite (Znth_map_69 (fun v => zcount_69 v prefix) base_vals j 0 0) by lia.
    rewrite Hhit.
    reflexivity.
  }
  unfold search_outer_state_69.
  repeat split.
  - lia.
  - lia.
  - replace (prefix_69 input (i + 1)) with (prefix ++ [x]).
    + unfold base_vals in Hseen_snoc.
      symmetry.
      exact Hseen_snoc.
    + unfold prefix_69, prefix, x.
      symmetry.
      apply sublist_snoc_Znth_69; lia.
  - replace (prefix_69 input (i + 1)) with (prefix ++ [x]).
    + rewrite Hcnts_base.
      apply counts_for_values_snoc_hit_replace_69.
      * apply seen_values_NoDup_69.
      * reflexivity.
      * exact Hj.
      * exact Hhit.
    + unfold prefix_69, prefix, x.
      symmetry.
      apply sublist_snoc_Znth_69; lia.
  - unfold hit_max_69.
    rewrite Hcnts_base.
    rewrite Hcnt_at, Hhit, Hmax_base.
    unfold search_prefix_69, prefix_69.
    rewrite sublist_snoc_Znth_69 by lia.
    fold prefix x.
    rewrite search_impl_snoc_69.
    unfold search_prefix_69, prefix_69 in Hmax_base.
    change (search_impl (sublist 0 i input)) with (search_impl prefix).
    change (zcount_69 x (sublist 0 i input)) with (zcount_69 x prefix).
    destruct (zcount_69 x prefix + 1 >=? x) eqn:Hqual; simpl.
    + destruct (x >? search_impl prefix) eqn:Hgt.
      * apply Z.gtb_lt in Hgt.
        rewrite Z.max_l by lia.
        reflexivity.
      * assert (x <= search_impl prefix).
        {
          destruct (Z.gtb_spec x (search_impl prefix)); try congruence; lia.
        }
        rewrite Z.max_r by lia.
        reflexivity.
    + reflexivity.
Qed.
