Load "../spec/109".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_109_pre_z (arr : list Z) : Prop :=
  problem_109_pre arr.

Definition problem_109_spec_z (arr : list Z) (result : bool) : Prop :=
  problem_109_spec arr result.

Definition drop_bit_109 (a b : Z) : Z :=
  if b <? a then 1 else 0.

Definition linear_drop_count_109 (l : list Z) : Z :=
  Z.of_nat
    (length
       (filter
          (fun p => snd p <? fst p)
          (combine l (tl l)))).

Definition wrap_drop_count_109 (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: _ => linear_drop_count_109 l + drop_bit_109 (last l h) h
  end.

Definition move_one_ball_safe_109 (arr : list Z) : Prop :=
  problem_109_pre_z arr.

Definition move_one_ball_prefix_109 (input : list Z) (i num : Z) : Prop :=
  1 <= i <= Zlength input /\
  num = linear_drop_count_109 (sublist 0 i input).

Definition move_one_ball_wrap_109 (input : list Z) (num : Z) : Prop :=
  num = wrap_drop_count_109 input /\
  move_one_ball_safe_109 input.

Lemma linear_drop_count_109_nonneg : forall l,
  0 <= linear_drop_count_109 l.
Proof.
  intro l. unfold linear_drop_count_109. lia.
Qed.

Lemma drop_bit_109_range : forall a b,
  0 <= drop_bit_109 a b <= 1.
Proof.
  intros a b. unfold drop_bit_109.
  destruct (b <? a); lia.
Qed.

Lemma linear_drop_count_109_cons_cons : forall a b t,
  linear_drop_count_109 (a :: b :: t) =
    drop_bit_109 a b + linear_drop_count_109 (b :: t).
Proof.
  intros a b t.
  unfold linear_drop_count_109, drop_bit_109.
  cbn [combine tl filter length fst snd].
  destruct (b <? a) eqn:E; cbn [length].
  - rewrite Nat2Z.inj_succ. lia.
  - lia.
Qed.

Lemma last_nonempty_default_irrel_109 : forall (l : list Z) d1 d2,
  l <> [] ->
  last l d1 = last l d2.
Proof.
  induction l as [|a [|b t] IH]; intros d1 d2 Hne; simpl; auto; try contradiction.
  apply IH. discriminate.
Qed.

Lemma last_cons_cons_109 : forall (a b : Z) (t : list Z) d1 d2,
  last (a :: b :: t) d1 = last (b :: t) d2.
Proof.
  intros a b t d1 d2. simpl.
  destruct t as [|c t]; simpl; auto.
  change (last (c :: t) d1 = last (c :: t) d2).
  apply last_nonempty_default_irrel_109. discriminate.
Qed.

Lemma linear_drop_count_109_zero_sorted : forall l,
  linear_drop_count_109 l = 0 ->
  sorted_list l.
Proof.
  induction l as [|a [|b t] IH]; intros Hzero; constructor; auto.
  - apply IH.
    rewrite linear_drop_count_109_cons_cons in Hzero.
    pose proof (linear_drop_count_109_nonneg (b :: t)).
    unfold drop_bit_109 in Hzero.
    destruct (b <? a); lia.
  - constructor.
    rewrite linear_drop_count_109_cons_cons in Hzero.
    pose proof (linear_drop_count_109_nonneg (b :: t)).
    unfold drop_bit_109 in Hzero.
    destruct (b <? a) eqn:E; [lia |].
    apply Z.ltb_ge in E. lia.
Qed.

Lemma sorted_linear_drop_count_109_zero : forall l,
  sorted_list l ->
  linear_drop_count_109 l = 0.
Proof.
  induction l as [|a [|b t] IH]; intros Hsorted; auto.
  rewrite linear_drop_count_109_cons_cons.
  inversion Hsorted as [|? ? Htail Hhd]; subst.
  inversion Hhd; subst.
  unfold drop_bit_109.
  replace (b <? a) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite IH by exact Htail.
  lia.
Qed.

Lemma linear_drop_count_109_app_cons : forall p hq q hp,
  p <> [] ->
  linear_drop_count_109 (p ++ hq :: q) =
    linear_drop_count_109 p + linear_drop_count_109 (hq :: q) +
    drop_bit_109 (last p hp) hq.
Proof.
  induction p as [|a p IH]; intros hq q hp Hp; [contradiction |].
  destruct p as [|b p].
  - simpl. rewrite linear_drop_count_109_cons_cons. simpl. lia.
  - simpl app. rewrite linear_drop_count_109_cons_cons.
    change (linear_drop_count_109 (b :: p ++ hq :: q))
      with (linear_drop_count_109 ((b :: p) ++ hq :: q)).
    rewrite (IH hq q b) by discriminate.
    rewrite linear_drop_count_109_cons_cons.
    rewrite last_cons_cons_109 with (d2 := b).
    lia.
Qed.

Lemma linear_drop_count_109_cons_app_cons : forall hp pt hq qt,
  linear_drop_count_109 (hp :: pt ++ hq :: qt) =
    linear_drop_count_109 (hp :: pt) + linear_drop_count_109 (hq :: qt) +
    drop_bit_109 (last (hp :: pt) hp) hq.
Proof.
  intros hp pt hq qt.
  change (linear_drop_count_109 ((hp :: pt) ++ (hq :: qt)) =
    linear_drop_count_109 (hp :: pt) + linear_drop_count_109 (hq :: qt) +
    drop_bit_109 (last (hp :: pt) hp) hq).
  apply linear_drop_count_109_app_cons. discriminate.
Qed.

Lemma last_app_cons_109 : forall (p : list Z) h q d1 d2,
  last (p ++ h :: q) d1 = last (h :: q) d2.
Proof.
  induction p as [|a p IH]; intros h q d1 d2.
  - destruct q as [|c q]; simpl; auto.
    change (last (c :: q) d1 = last (c :: q) d2).
    apply last_nonempty_default_irrel_109. discriminate.
  - simpl.
    destruct p as [|b p].
    + simpl. destruct q as [|c q]; simpl; auto.
      change (last (c :: q) d1 = last (c :: q) d2).
      apply last_nonempty_default_irrel_109. discriminate.
    + simpl.
      change (last ((b :: p) ++ h :: q) d1 = last (h :: q) d2).
      rewrite (IH h q d1 d2). reflexivity.
Qed.

Lemma last_cons_app_cons_109 : forall (hp : Z) (pt : list Z) (hq : Z) (qt : list Z) (d1 d2 : Z),
  last (hp :: pt ++ hq :: qt) d1 = last (hq :: qt) d2.
Proof.
  intros hp pt hq qt d1 d2.
  revert hp d1.
  induction pt as [|x xs IH]; intros hp d1.
  - simpl. apply (last_cons_cons_109 hp hq qt d1 d2).
  - simpl. apply IH.
Qed.

Lemma wrap_drop_count_109_app_comm : forall p q,
  wrap_drop_count_109 (p ++ q) = wrap_drop_count_109 (q ++ p).
Proof.
  intros p q.
  destruct p as [|hp pt]; [rewrite app_nil_r; reflexivity |].
  destruct q as [|hq qt]; [simpl; rewrite app_nil_r; reflexivity |].
  unfold wrap_drop_count_109.
  cbn [app].
  rewrite linear_drop_count_109_cons_app_cons.
  rewrite linear_drop_count_109_cons_app_cons.
  replace (last (hp :: pt ++ hq :: qt) hp) with (last (hq :: qt) hq).
  2: { symmetry. apply last_cons_app_cons_109. }
  replace (last (hq :: qt ++ hp :: pt) hq) with (last (hp :: pt) hp).
  2: { symmetry. apply last_cons_app_cons_109. }
  remember (linear_drop_count_109 (hp :: pt)) as A.
  remember (linear_drop_count_109 (hq :: qt)) as B.
  remember (drop_bit_109 (last (hp :: pt) hp) hq) as C.
  remember (drop_bit_109 (last (hq :: qt) hq) hp) as D.
  lia.
Qed.

Fixpoint min_list_109 (h : Z) (t : list Z) : Z :=
  match t with
  | [] => h
  | x :: xs => Z.min h (min_list_109 x xs)
  end.

Lemma min_list_109_in : forall h t,
  In (min_list_109 h t) (h :: t).
Proof.
  intros h t. revert h.
  induction t as [|x xs IH]; intros h; simpl; auto.
  destruct (Z.min_spec h (min_list_109 x xs)) as [[_ Hmin] | [_ Hmin]];
    rewrite Hmin; auto.
  right. apply IH.
Qed.

Lemma min_list_109_le : forall h t x,
  In x (h :: t) ->
  min_list_109 h t <= x.
Proof.
  intros h t. revert h.
  induction t as [|y ys IH]; intros h x Hin; simpl in *.
  - destruct Hin as [<- | []]. lia.
  - destruct Hin as [<- | [<- | Hin]].
    + apply Z.le_min_l.
    + eapply Z.le_trans; [apply Z.le_min_r |].
      apply IH. left. reflexivity.
    + eapply Z.le_trans; [apply Z.le_min_r |].
      apply IH. right. exact Hin.
Qed.

Lemma last_in_109 : forall (l : list Z) d,
  l <> [] ->
  In (last l d) l.
Proof.
  induction l as [|a [|b t] IH]; intros d Hne; simpl; auto; try contradiction.
  right. apply IH. discriminate.
Qed.

Lemma in_rotate_back_109 : forall (x m : Z) prefix suffix,
  In x (m :: suffix ++ prefix) ->
  In x (prefix ++ m :: suffix).
Proof.
  intros x m prefix suffix Hin.
  simpl in Hin.
  rewrite in_app_iff in *.
  destruct Hin as [<- | Hin].
  - right. left. reflexivity.
  - destruct Hin as [Hin | Hin]; auto.
    right. right. exact Hin.
Qed.

Lemma min_head_tail_last_drop_109 : forall m rest original,
  rest <> [] ->
  NoDup (original) ->
  original = [] \/ In m original ->
  (forall x, In x original -> m <= x) ->
  (forall x, In x rest -> In x original) ->
  ~ In m rest ->
  drop_bit_109 (last (m :: rest) m) m = 1.
Proof.
  intros m rest original Hrest _ _ Hmin Hin_orig Hnotin.
  unfold drop_bit_109.
  assert (Hin_last_rest : In (last rest m) rest).
  { apply last_in_109. exact Hrest. }
  assert (Hle : m <= last rest m) by (apply Hmin, Hin_orig, Hin_last_rest).
  assert (Hneq : last rest m <> m).
  { intro Heq. apply Hnotin. rewrite <- Heq. exact Hin_last_rest. }
  replace (last (m :: rest) m) with (last rest m).
  2: {
    destruct rest as [|r rs]; [contradiction |].
    destruct rs as [|s ss]; simpl; auto.
  }
  replace (m <? last rest m) with true.
  - reflexivity.
  - symmetry. apply Z.ltb_lt. lia.
Qed.

Lemma wrap_drop_count_109_min_rotation_sorted : forall input,
  problem_109_pre_z input ->
  wrap_drop_count_109 input < 2 ->
  rotation_sorted input.
Proof.
  intros input Hnodup Hcount.
  destruct input as [|h t].
  - exists [], []. simpl. split; [reflexivity | constructor].
  - set (m := min_list_109 h t).
    assert (Hin_m : In m (h :: t)) by (subst m; apply min_list_109_in).
    destruct (in_split _ _ Hin_m) as [prefix [suffix Hsplit]].
    exists prefix, (m :: suffix).
    split; [exact Hsplit |].
    assert (Hrot_count : wrap_drop_count_109 (m :: suffix ++ prefix) < 2).
    { change (wrap_drop_count_109 ((m :: suffix) ++ prefix) < 2).
      rewrite (wrap_drop_count_109_app_comm (m :: suffix) prefix).
      rewrite <- Hsplit.
      exact Hcount. }
    destruct (suffix ++ prefix) as [|r rs] eqn:Hrest.
    + change (sorted_list (m :: (suffix ++ prefix))).
      rewrite Hrest. repeat constructor.
    + apply linear_drop_count_109_zero_sorted.
      unfold wrap_drop_count_109 in Hrot_count.
      simpl in Hrot_count.
      assert (Hdrop : drop_bit_109 (last (m :: r :: rs) m) m = 1).
      { eapply min_head_tail_last_drop_109 with (original := prefix ++ m :: suffix).
        - discriminate.
        - rewrite <- Hsplit. exact Hnodup.
        - right. rewrite in_app_iff. right. left. reflexivity.
        - intros x Hin.
          subst m. apply min_list_109_le.
          rewrite Hsplit. exact Hin.
        - intros x Hin.
          rewrite <- Hrest in Hin.
          rewrite in_app_iff in Hin.
          rewrite in_app_iff.
          destruct Hin as [Hin_suffix | Hin_prefix].
          + right. right. exact Hin_suffix.
          + left. exact Hin_prefix.
        - pose proof (NoDup_remove_2 prefix suffix m) as Hremove.
          rewrite <- Hrest.
          rewrite in_app_iff.
          intro Hin.
          assert (Hnodup_split : NoDup (prefix ++ m :: suffix)).
          { rewrite <- Hsplit. exact Hnodup. }
          apply (Hremove Hnodup_split).
          rewrite in_app_iff in *.
          destruct Hin as [Hin | Hin]; auto.
      }
      change (linear_drop_count_109 (m :: r :: rs) +
        drop_bit_109 (last (m :: r :: rs) m) m < 2) in Hrot_count.
      rewrite Hdrop in Hrot_count.
      pose proof (linear_drop_count_109_nonneg (m :: r :: rs)).
      change (linear_drop_count_109 (m :: (suffix ++ prefix)) = 0).
      rewrite Hrest.
      lia.
Qed.

Lemma sorted_wrap_drop_count_109_lt2 : forall l,
  sorted_list l ->
  wrap_drop_count_109 l < 2.
Proof.
  intros l Hsorted.
  destruct l as [|h t]; [simpl; lia |].
  unfold wrap_drop_count_109.
  rewrite sorted_linear_drop_count_109_zero by exact Hsorted.
  pose proof (drop_bit_109_range (last (h :: t) h) h).
  lia.
Qed.

Lemma rotation_sorted_wrap_drop_count_109_lt2 : forall input,
  rotation_sorted input ->
  wrap_drop_count_109 input < 2.
Proof.
  intros input [prefix [suffix [Hsplit Hsorted]]].
  rewrite Hsplit.
  rewrite wrap_drop_count_109_app_comm.
  apply sorted_wrap_drop_count_109_lt2.
  exact Hsorted.
Qed.

Lemma move_one_ball_safe_109_equiv : forall input,
  problem_109_pre_z input ->
  (wrap_drop_count_109 input < 2 <-> rotation_sorted input).
Proof.
  intros input Hpre. split.
  - apply wrap_drop_count_109_min_rotation_sorted. exact Hpre.
  - apply rotation_sorted_wrap_drop_count_109_lt2.
Qed.

Lemma linear_drop_count_109_bound : forall l,
  0 < Zlength l ->
  linear_drop_count_109 l <= Zlength l - 1.
Proof.
  intros l Hlen.
  destruct l as [|h t]; [change (Zlength (@nil Z)) with 0 in Hlen; lia |].
  unfold linear_drop_count_109.
  pose proof
    (filter_length_le
       (fun p : Z * Z => snd p <? fst p)
       (combine (h :: t) (tl (h :: t)))) as Hfilter.
  assert (Hcomb :
    (length (combine (h :: t) (tl (h :: t))) <= length t)%nat).
  { destruct t as [|y ys]; simpl; [lia |].
    assert (length (combine (y :: ys) ys) <= length ys)%nat.
    { rewrite length_combine. apply Nat.le_min_r. }
    apply le_n_S. exact H. }
  assert (Hle_nat :
    (length
       (filter (fun p : Z * Z => (snd p <? fst p)%Z)
          (combine (h :: t) (tl (h :: t)))) <= length t)%nat) by lia.
  apply Nat2Z.inj_le in Hle_nat.
  rewrite Zlength_cons, Zlength_correct.
  lia.
Qed.

Lemma move_one_ball_prefix_109_bound : forall input i num,
  move_one_ball_prefix_109 input i num ->
  num <= i - 1.
Proof.
  intros input i num [Hbounds Hnum].
  rewrite Hnum.
  eapply Z.le_trans.
  - apply linear_drop_count_109_bound.
    rewrite Zlength_sublist by lia. lia.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma move_one_ball_prefix_109_init : forall input,
  0 < Zlength input ->
  move_one_ball_prefix_109 input 1 0.
Proof.
  intros input Hlen.
  unfold move_one_ball_prefix_109, linear_drop_count_109.
  split; [lia |].
  replace (sublist 0 1 input) with [Znth 0 input 0].
  - simpl. reflexivity.
  - symmetry. apply sublist_single. lia.
Qed.

Lemma combine_app_single_109 : forall (l1 l2 : list Z) (a b : Z),
  length l1 = length l2 ->
  combine (l1 ++ [a]) (l2 ++ [b]) = combine l1 l2 ++ [(a, b)].
Proof.
  induction l1 as [|x xs IH]; intros l2 a b Hlen;
    destruct l2 as [|y ys]; simpl in *; try discriminate; auto.
  f_equal. apply IH. lia.
Qed.

Lemma combine_snoc_tl_109 : forall (l : list Z) a b d,
  l <> [] ->
  combine (l ++ [a]) (tl l ++ [b]) =
    combine l (tl l) ++ [(last l d, b)].
Proof.
  induction l as [|x xs IH]; intros a b d Hne; [contradiction |].
  destruct xs as [|y ys].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH. discriminate.
Qed.

Lemma last_snoc_109 : forall (l : list Z) x d,
  last (l ++ [x]) d = x.
Proof.
  induction l as [|h t IH]; intros x d; simpl; auto.
  destruct t as [|h2 t2]; simpl; auto.
  apply IH.
Qed.

Lemma sublist_0_snoc_109 : forall input i,
  1 <= i < Zlength input ->
  sublist 0 (i + 1) input = sublist 0 i input ++ [Znth i input 0].
Proof.
  intros input i Hi.
  rewrite (sublist_split 0 (i + 1) i input) by lia.
  rewrite (sublist_single 0 i input) by lia.
  reflexivity.
Qed.

Lemma tl_sublist_snoc_109 : forall input i,
  1 <= i < Zlength input ->
  tl (sublist 0 (i + 1) input) = sublist 1 i input ++ [Znth i input 0].
Proof.
  intros input i Hi.
  rewrite sublist_0_snoc_109 by lia.
  destruct (sublist 0 i input) as [|h t] eqn:Hsub.
  - assert (Hlen_sub : Zlength (sublist 0 i input) = i).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite Hsub in Hlen_sub.
    change (Zlength (@nil Z)) with 0 in Hlen_sub.
    lia.
  - simpl.
    replace t with (sublist 1 i input); [reflexivity |].
    assert (Hsplit : sublist 0 i input =
      sublist 0 1 input ++ sublist 1 i input).
    { rewrite (sublist_split 0 i 1 input) by lia. reflexivity. }
    rewrite Hsub in Hsplit.
    replace (sublist 0 1 input) with [Znth 0 input 0] in Hsplit
      by (symmetry; apply sublist_single; lia).
    simpl in Hsplit. inversion Hsplit. reflexivity.
Qed.

Lemma tl_sublist_prefix_109 : forall (input : list Z) i,
  1 <= i <= Zlength input ->
  tl (sublist 0 i input) = sublist 1 i input.
Proof.
  intros input i Hi.
  destruct (sublist 0 i input) as [|h t] eqn:Hsub.
  - assert (Hlen_sub : Zlength (sublist 0 i input) = i).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite Hsub in Hlen_sub.
    change (Zlength (@nil Z)) with 0 in Hlen_sub.
    lia.
  - simpl.
    replace t with (sublist 1 i input); [reflexivity |].
    assert (Hsplit : sublist 0 i input =
      sublist 0 1 input ++ sublist 1 i input).
    { rewrite (sublist_split 0 i 1 input) by lia. reflexivity. }
    rewrite Hsub in Hsplit.
    replace (sublist 0 1 input) with [Znth 0 input 0] in Hsplit
      by (symmetry; apply sublist_single; lia).
    simpl in Hsplit. inversion Hsplit. reflexivity.
Qed.

Lemma last_sublist_0_i_109 : forall input i d,
  1 <= i <= Zlength input ->
  last (sublist 0 i input) d = Znth (i - 1) input 0.
Proof.
  intros input i d Hi.
  replace (sublist 0 i input)
    with (sublist 0 (i - 1) input ++ [Znth (i - 1) input 0]).
  - rewrite last_snoc_109. reflexivity.
  - rewrite (sublist_split 0 i (i - 1) input) by lia.
    replace (sublist (i - 1) i input) with [Znth (i - 1) input 0]
      by (assert (Hsingle :
            sublist (i - 1) (i - 1 + 1) input =
              [Znth (i - 1) input 0])
            by (apply sublist_single; lia);
          replace i with (i - 1 + 1) by lia;
          replace (i - 1 + 1 - 1) with (i - 1) by lia;
          symmetry; exact Hsingle).
    reflexivity.
Qed.

Lemma last_as_Znth_109 : forall h t,
  last (h :: t) h = Znth (Zlength (h :: t) - 1) (h :: t) 0.
Proof.
  intros h t.
  assert (Hlen : 1 <= Zlength (h :: t) <= Zlength (h :: t)).
  { rewrite Zlength_cons.
    pose proof (Zlength_nonneg t). lia. }
  pose proof (last_sublist_0_i_109 (h :: t) (Zlength (h :: t)) h Hlen) as Hlast.
  assert (Hsame : sublist 0 (Zlength (h :: t)) (h :: t) = h :: t).
  { apply sublist_self. reflexivity. }
  rewrite Hsame in Hlast.
  exact Hlast.
Qed.

Lemma linear_drop_count_109_step : forall input i,
  1 <= i < Zlength input ->
  linear_drop_count_109 (sublist 0 (i + 1) input) =
    linear_drop_count_109 (sublist 0 i input) +
    drop_bit_109 (Znth (i - 1) input 0) (Znth i input 0).
Proof.
  intros input i Hi.
  unfold linear_drop_count_109, drop_bit_109.
  replace (tl (sublist 0 (i + 1) input))
    with (sublist 1 i input ++ [Znth i input 0])
    by (symmetry; apply tl_sublist_snoc_109; lia).
  replace (tl (sublist 0 i input))
    with (sublist 1 i input)
    by (symmetry; apply tl_sublist_prefix_109; lia).
  replace (sublist 0 (i + 1) input)
    with (sublist 0 i input ++ [Znth i input 0])
    by (symmetry; apply sublist_0_snoc_109; lia).
  rewrite combine_snoc_tl_109 with (d := 0).
  - rewrite last_sublist_0_i_109 with (d := 0) by lia.
    replace (tl (sublist 0 i input))
      with (sublist 1 i input)
      by (symmetry; apply tl_sublist_prefix_109; lia).
    rewrite filter_app. rewrite app_length. simpl.
    destruct (Znth i input 0 <? Znth (i - 1) input 0);
      simpl; rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ; simpl; zify; lia.
  - intro Hempty.
    assert (Hlen_sub : Zlength (sublist 0 i input) = i).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite Hempty in Hlen_sub.
    change (Zlength (@nil Z)) with 0 in Hlen_sub.
    lia.
Qed.

Lemma move_one_ball_prefix_109_step_drop : forall input i num,
  1 <= i < Zlength input ->
  move_one_ball_prefix_109 input i num ->
  Znth i input 0 < Znth (i - 1) input 0 ->
  move_one_ball_prefix_109 input (i + 1) (num + 1).
Proof.
  intros input i num Hi [Hbounds Hnum] Hdrop.
  split; [lia |].
  rewrite linear_drop_count_109_step by lia.
  unfold drop_bit_109.
  replace (Znth i input 0 <? Znth (i - 1) input 0) with true
    by (symmetry; apply Z.ltb_lt; lia).
  lia.
Qed.

Lemma move_one_ball_prefix_109_step_nodrop : forall input i num,
  1 <= i < Zlength input ->
  move_one_ball_prefix_109 input i num ->
  Znth i input 0 >= Znth (i - 1) input 0 ->
  move_one_ball_prefix_109 input (i + 1) num.
Proof.
  intros input i num Hi [Hbounds Hnum] Hnodrop.
  split; [lia |].
  rewrite linear_drop_count_109_step by lia.
  unfold drop_bit_109.
  replace (Znth i input 0 <? Znth (i - 1) input 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  lia.
Qed.

Lemma move_one_ball_wrap_109_step_drop : forall input num,
  0 < Zlength input ->
  move_one_ball_safe_109 input ->
  move_one_ball_prefix_109 input (Zlength input) num ->
  Znth (Zlength input - 1) input 0 > Znth 0 input 0 ->
  move_one_ball_wrap_109 input (num + 1).
Proof.
  intros input num Hlen Hsafe [_ Hnum] Hdrop.
  unfold move_one_ball_wrap_109, wrap_drop_count_109, drop_bit_109 in *.
  split; [|exact Hsafe].
  destruct input as [|h t]; [change (Zlength (@nil Z)) with 0 in Hlen; lia |].
  simpl.
  assert (Hsub : sublist 0 (Zlength (h :: t)) (h :: t) = h :: t).
  { apply sublist_self. reflexivity. }
  rewrite Hsub in Hnum.
  rewrite Hnum.
  change (Znth 0 (h :: t) 0) with h.
  change (Znth 0 (h :: t) 0) with h in Hdrop.
  replace (match t with
           | [] => h
           | _ :: _ => last t h
           end)
    with (Znth (Zlength (h :: t) - 1) (h :: t) 0)
    by (symmetry; apply last_as_Znth_109).
  replace (h <? Znth (Zlength (h :: t) - 1) (h :: t) 0) with true
    by (symmetry; apply Z.ltb_lt; lia).
  lia.
Qed.

Lemma move_one_ball_wrap_109_step_nodrop : forall input num,
  0 < Zlength input ->
  move_one_ball_safe_109 input ->
  move_one_ball_prefix_109 input (Zlength input) num ->
  Znth (Zlength input - 1) input 0 <= Znth 0 input 0 ->
  move_one_ball_wrap_109 input num.
Proof.
  intros input num Hlen Hsafe [_ Hnum] Hnodrop.
  unfold move_one_ball_wrap_109, wrap_drop_count_109, drop_bit_109 in *.
  split; [|exact Hsafe].
  destruct input as [|h t]; [change (Zlength (@nil Z)) with 0 in Hlen; lia |].
  simpl.
  assert (Hsub : sublist 0 (Zlength (h :: t)) (h :: t) = h :: t).
  { apply sublist_self. reflexivity. }
  rewrite Hsub in Hnum.
  rewrite Hnum.
  change (Znth 0 (h :: t) 0) with h.
  change (Znth 0 (h :: t) 0) with h in Hnodrop.
  replace (match t with
           | [] => h
           | _ :: _ => last t h
           end)
    with (Znth (Zlength (h :: t) - 1) (h :: t) 0)
    by (symmetry; apply last_as_Znth_109).
  replace (h <? Znth (Zlength (h :: t) - 1) (h :: t) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  lia.
Qed.

Lemma problem_109_empty_true : problem_109_spec_z [] true.
Proof.
  unfold problem_109_spec_z, problem_109_spec, rotation_sorted.
  split; intros _.
  - exists [], []. simpl. split; [reflexivity | constructor].
  - reflexivity.
Qed.

Lemma move_one_ball_wrap_109_true : forall input num,
  move_one_ball_wrap_109 input num ->
  num < 2 ->
  problem_109_spec_z input true.
Proof.
  intros input num [Hwrap Hsafe] Hlt.
  unfold problem_109_spec_z, problem_109_spec.
  split; intros _.
  - apply (proj1 (move_one_ball_safe_109_equiv input Hsafe)).
    rewrite <- Hwrap. exact Hlt.
  - reflexivity.
Qed.

Lemma move_one_ball_wrap_109_false : forall input num,
  move_one_ball_wrap_109 input num ->
  num >= 2 ->
  problem_109_spec_z input false.
Proof.
  intros input num [Hwrap Hsafe] Hge.
  unfold problem_109_spec_z, problem_109_spec.
  split; intros H.
  - discriminate.
  - exfalso.
    pose proof (proj2 (move_one_ball_safe_109_equiv input Hsafe) H) as Hcount.
    rewrite <- Hwrap in Hcount. lia.
Qed.
