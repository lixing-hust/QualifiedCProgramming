Load "../spec/123".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_123_pre_z (n : Z) : Prop :=
  problem_123_pre n.

Definition problem_123_spec_z (n : Z) (result : list Z) : Prop :=
  problem_123_spec n result.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition collatz_next_123 (x : Z) : Z :=
  if Z.even x then x / 2 else 3 * x + 1.

Definition odd_z_123 (x : Z) : bool := Z.odd x.

Definition odd_filter_123 (l : list Z) : list Z :=
  filter odd_z_123 l.

Definition odd_count_123 (l : list Z) : Z :=
  Z.of_nat (length (odd_filter_123 l)).

Lemma Zlength_odd_filter_123 : forall l,
  Zlength (odd_filter_123 l) = odd_count_123 l.
Proof.
  intro l.
  unfold odd_count_123.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Definition collatz_safe_seq_123 (seq : list Z) : Prop :=
  Forall (fun x =>
    0 < x < INT_MAX /\
    3 * x + 1 <= INT_MAX) seq /\
  Zlength seq + 2 < INT_MAX.

Definition collatz_safe_123 (n : Z) : Prop :=
  exists seq,
    collatz_list n seq /\
    collatz_safe_seq_123 seq.

Definition collatz_count_state_123 (n cur count : Z) : Prop :=
  exists prefix suffix,
    collatz_list n (prefix ++ cur :: suffix) /\
    collatz_safe_seq_123 (prefix ++ cur :: suffix) /\
    0 < cur /\ cur < INT_MAX /\ 3 * cur + 1 <= INT_MAX /\
    count = 1 + odd_count_123 prefix /\
    0 < count /\ count + 1 < INT_MAX.

Definition collatz_final_count_123 (n count : Z) : Prop :=
  exists seq,
    collatz_list n seq /\
    collatz_safe_seq_123 seq /\
    count = odd_count_123 seq /\
    0 < count /\ count + 1 < INT_MAX.

Definition collatz_output_state_123
  (n count cur : Z) (output : list Z) : Prop :=
  exists prefix suffix,
    collatz_list n (prefix ++ cur :: suffix) /\
    collatz_safe_seq_123 (prefix ++ cur :: suffix) /\
    collatz_final_count_123 n count /\
    count = odd_count_123 (prefix ++ cur :: suffix) /\
    0 < cur /\ cur < INT_MAX /\ 3 * cur + 1 <= INT_MAX /\
    output = 1 :: odd_filter_123 prefix.

Lemma odd_count_nil_123 :
  odd_count_123 [] = 0.
Proof. reflexivity. Qed.

Lemma odd_count_app_123 : forall l r,
  odd_count_123 (l ++ r) = odd_count_123 l + odd_count_123 r.
Proof.
  intros l r.
  unfold odd_count_123, odd_filter_123.
  rewrite filter_app, length_app, Nat2Z.inj_add.
  reflexivity.
Qed.

Lemma odd_count_single_odd_123 : forall x,
  Z.odd x = true ->
  odd_count_123 [x] = 1.
Proof.
  intros x Hodd.
  unfold odd_count_123, odd_filter_123.
  simpl. unfold odd_z_123. rewrite Hodd. reflexivity.
Qed.

Lemma odd_count_single_even_123 : forall x,
  Z.odd x = false ->
  odd_count_123 [x] = 0.
Proof.
  intros x Hodd.
  unfold odd_count_123, odd_filter_123.
  simpl. unfold odd_z_123. rewrite Hodd. reflexivity.
Qed.

Lemma odd_count_cons_123 : forall x xs,
  odd_count_123 (x :: xs) =
  (if Z.odd x then 1 else 0) + odd_count_123 xs.
Proof.
  intros x xs.
  unfold odd_count_123, odd_filter_123, odd_z_123.
  simpl.
  destruct (Z.odd x).
  - change (Z.of_nat (S (length (filter (fun x : Z => Z.odd x) xs))) =
            1 + Z.of_nat (length (filter (fun x : Z => Z.odd x) xs))).
    rewrite Nat2Z.inj_succ. lia.
  - reflexivity.
Qed.

Lemma odd_count_app_single_odd_123 : forall l x,
  Z.odd x = true ->
  odd_count_123 (l ++ [x]) = odd_count_123 l + 1.
Proof.
  intros l x Hodd.
  rewrite odd_count_app_123, odd_count_single_odd_123 by exact Hodd.
  lia.
Qed.

Lemma odd_count_app_single_even_123 : forall l x,
  Z.odd x = false ->
  odd_count_123 (l ++ [x]) = odd_count_123 l.
Proof.
  intros l x Hodd.
  rewrite odd_count_app_123, odd_count_single_even_123 by exact Hodd.
  lia.
Qed.

Lemma odd_count_le_Zlength_123 : forall l,
  0 <= odd_count_123 l /\ odd_count_123 l <= Zlength l.
Proof.
  intro l.
  unfold odd_count_123, odd_filter_123.
  rewrite Zlength_correct.
  split; [lia|].
  apply Nat2Z.inj_le.
  pose proof (filter_length odd_z_123 l).
  lia.
Qed.

Lemma z_odd_of_mod_one_123 : forall x,
  x mod 2 = 1 ->
  Z.odd x = true.
Proof.
  intros x Hmod.
  pose proof (Zmod_odd x) as Hodd.
  rewrite Hmod in Hodd.
  destruct (Z.odd x); [reflexivity|discriminate].
Qed.

Lemma z_even_false_of_mod_one_123 : forall x,
  x mod 2 = 1 ->
  Z.even x = false.
Proof.
  intros x Hmod.
  pose proof (z_odd_of_mod_one_123 _ Hmod) as Hodd.
  rewrite Zeven.Zeven_odd_bool, Hodd.
  reflexivity.
Qed.

Lemma z_even_true_of_not_mod_one_123 : forall x,
  0 < x ->
  x mod 2 <> 1 ->
  Z.even x = true.
Proof.
  intros x Hpos Hmod.
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)) as Hbound.
  assert (x mod 2 = 0) by lia.
  pose proof (Zmod_odd x) as Hodd.
  rewrite H in Hodd.
  destruct (Z.odd x) eqn:?; [discriminate|].
  rewrite Zeven.Zeven_odd_bool, Heqb.
  reflexivity.
Qed.

Lemma collatz_pair_after_prefix_123 : forall prefix cur next rest,
  Forall (fun p => collatz_step (fst p) (snd p))
    (combine (prefix ++ cur :: next :: rest)
             (tl (prefix ++ cur :: next :: rest))) ->
  collatz_step cur next.
Proof.
  intros prefix cur next rest Hf.
  rewrite Forall_forall in Hf.
  apply (Hf (cur, next)).
  clear Hf.
  induction prefix as [|h prefix IH].
  - simpl. auto.
  - destruct prefix as [|h' prefix'].
    + simpl. auto.
    + simpl. right. exact IH.
Qed.

Lemma no_collatz_step_from_one_123 : forall x,
  ~ collatz_step 1 x.
Proof.
  intros x Hstep.
  unfold collatz_step in Hstep.
  tauto.
Qed.

Lemma last_app_single_123 : forall l x,
  last (l ++ [x]) 0 = x.
Proof.
  induction l as [|h t IH]; intros x; simpl; auto.
  destruct t; simpl in *; auto.
Qed.

Lemma last_after_prefix_123 : forall prefix cur next rest,
  last (prefix ++ cur :: next :: rest) 0 = last (next :: rest) 0.
Proof.
  induction prefix as [|h prefix IH]; intros cur next rest; simpl; auto.
  destruct prefix; simpl in *; auto.
Qed.

Lemma odd_count_pos_of_last_one_123 : forall l,
  l <> [] ->
  last l 0 = 1 ->
  1 <= odd_count_123 l.
Proof.
  induction l as [|h t IH]; intros Hne Hlast.
  - contradiction Hne; reflexivity.
  - destruct t as [|h' t'].
    + simpl in Hlast. subst h.
      unfold odd_count_123, odd_filter_123, odd_z_123.
      simpl. reflexivity.
    + simpl in Hlast.
      assert (1 <= odd_count_123 (h' :: t')).
      { apply IH; [discriminate | exact Hlast]. }
      rewrite odd_count_cons_123.
      destruct (Z.odd h); lia.
Qed.

Lemma suffix_empty_at_one_123 : forall n prefix suffix,
  collatz_list n (prefix ++ 1 :: suffix) ->
  suffix = [].
Proof.
  intros n prefix suffix Hseq.
  destruct suffix as [|next rest]; [reflexivity|].
  destruct Hseq as [_ [_ [_ Hsteps]]].
  pose proof (collatz_pair_after_prefix_123 prefix 1 next rest Hsteps) as Hstep.
  exfalso. apply (no_collatz_step_from_one_123 next). exact Hstep.
Qed.

Lemma collatz_safe_head_bounds_123 : forall n,
  collatz_safe_123 n ->
  0 < n /\ n < INT_MAX /\ 3 * n + 1 <= INT_MAX.
Proof.
  intros n Hsafe.
  destruct Hsafe as [seq [Hseq Hsafe_seq]].
  destruct seq as [|h t].
  - destruct Hseq as [Hne _]. contradiction Hne; reflexivity.
  - destruct Hseq as [_ [Hhd [_ _]]].
    destruct Hsafe_seq as [Hforall _].
    simpl in Hhd. subst h.
    inversion Hforall as [|? ? Hh _]; subst.
    destruct Hh as [[Hpos Hint] Hstep].
    repeat split; assumption.
Qed.

Lemma collatz_count_state_init_123 : forall n,
  problem_123_pre_z n ->
  collatz_safe_123 n ->
  collatz_count_state_123 n n 1.
Proof.
  intros n _ Hsafe.
  destruct Hsafe as [seq [Hseq Hsafe_seq]].
  destruct seq as [|h t].
  - destruct Hseq as [Hne _]. contradiction Hne; reflexivity.
  - exists [], t.
    pose proof Hseq as Hseq_full.
    destruct Hseq as [_ [Hhd [_ _]]].
    destruct Hsafe_seq as [Hforall Hlen].
    simpl in Hhd. subst h.
    inversion Hforall as [|? ? Hh _]; subst.
    destruct Hh as [[Hn_pos Hn_int] Hn_step].
    split; [exact Hseq_full|].
    split; [split; [exact Hforall | exact Hlen]|].
    split; [exact Hn_pos|].
    split; [exact Hn_int|].
    split; [exact Hn_step|].
    split.
    + unfold odd_count_123, odd_filter_123; cbn; lia.
    + lia.
Qed.

Lemma collatz_count_state_odd_step_123 : forall n cur count,
  0 < cur ->
  cur mod 2 = 1 ->
  cur <> 1 ->
  collatz_count_state_123 n cur count ->
  collatz_count_state_123 n (3 * cur + 1) (count + 1).
Proof.
  intros n cur count Hpos Hmod Hne Hstate.
  destruct Hstate as [prefix [suffix [Hseq [Hsafe Hrest]]]].
  destruct Hrest as [Hcur_pos [Hcur_lt [Hcur_step_bound [Hcount Hcbounds]]]].
  destruct Hcbounds as [Hcount_pos Hcount_next].
  destruct suffix as [|next rest].
  - destruct Hseq as [_ [_ [Hlast _]]].
    rewrite last_app_single_123 in Hlast.
    lia.
  - pose proof Hseq as Hseq_full.
    pose proof Hsafe as Hsafe_full.
    destruct Hseq as [Hnonempty [Hhd [Hlast Hsteps]]].
    destruct Hsafe as [Hforall Hlen].
    pose proof (collatz_pair_after_prefix_123 prefix cur next rest Hsteps)
      as Hpair.
    unfold collatz_step in Hpair.
    destruct Hpair as [_ Hnext].
    rewrite z_even_false_of_mod_one_123 in Hnext by exact Hmod.
    subst next.
    exists (prefix ++ [cur]), rest.
    rewrite <- app_assoc. simpl.
    split; [exact Hseq_full|].
    split; [exact Hsafe_full|].
    rewrite Forall_forall in Hforall.
    assert (Hnext_bounds :
      0 < 3 * cur + 1 < INT_MAX /\ 3 * (3 * cur + 1) + 1 <= INT_MAX).
    { apply Hforall.
      apply in_or_app. right. simpl. auto. }
    destruct Hnext_bounds as [[Hnext_pos Hnext_lt] Hnext_step].
    split; [exact Hnext_pos|].
    split; [exact Hnext_lt|].
    split; [exact Hnext_step|].
    split.
    + pose proof (odd_count_app_single_odd_123 prefix cur
        (z_odd_of_mod_one_123 cur Hmod)) as Hoddcount.
      rewrite Hcount, Hoddcount.
      change (1 + odd_count_123 prefix + 1 =
              1 + (odd_count_123 prefix + 1)).
      lia.
    + split.
      * lia.
      * subst count.
        assert (Hseq_len :
          Zlength (prefix ++ cur :: 3 * cur + 1 :: rest) =
          Zlength prefix + 2 + Zlength rest).
        { rewrite Zlength_app.
          rewrite !Zlength_cons.
          lia. }
        rewrite Hseq_len in Hlen.
        pose proof (odd_count_le_Zlength_123 prefix) as [_ Hle].
        pose proof (Zlength_nonneg rest).
        lia.
Qed.

Lemma collatz_count_state_even_step_123 : forall n cur count,
  0 < cur ->
  cur mod 2 <> 1 ->
  cur <> 1 ->
  collatz_count_state_123 n cur count ->
  collatz_count_state_123 n (cur ÷ 2) count.
Proof.
  intros n cur count Hpos Hmod Hne Hstate.
  destruct Hstate as [prefix [suffix [Hseq [Hsafe Hrest]]]].
  destruct Hrest as [Hcur_pos [Hcur_lt [Hcur_step_bound [Hcount Hcbounds]]]].
  destruct Hcbounds as [Hcount_pos Hcount_next].
  destruct suffix as [|next rest].
  - destruct Hseq as [_ [_ [Hlast _]]].
    rewrite last_app_single_123 in Hlast.
    lia.
  - pose proof Hseq as Hseq_full.
    pose proof Hsafe as Hsafe_full.
    destruct Hseq as [Hnonempty [Hhd [Hlast Hsteps]]].
    destruct Hsafe as [Hforall Hlen].
    pose proof (collatz_pair_after_prefix_123 prefix cur next rest Hsteps)
      as Hpair.
    unfold collatz_step in Hpair.
    destruct Hpair as [_ Hnext].
    pose proof (z_even_true_of_not_mod_one_123 _ Hpos Hmod) as Heven.
    rewrite Heven in Hnext.
    rewrite <- (Z.quot_div_nonneg cur 2) in Hnext by lia.
    subst next.
    exists (prefix ++ [cur]), rest.
    rewrite <- app_assoc. simpl.
    split; [exact Hseq_full|].
    split; [exact Hsafe_full|].
    rewrite Forall_forall in Hforall.
    assert (Hnext_bounds :
      0 < cur ÷ 2 < INT_MAX /\ 3 * (cur ÷ 2) + 1 <= INT_MAX).
    { apply Hforall.
      apply in_or_app. right. simpl. auto. }
    destruct Hnext_bounds as [[Hnext_pos Hnext_lt] Hnext_step].
    split; [exact Hnext_pos|].
    split; [exact Hnext_lt|].
    split; [exact Hnext_step|].
    split.
    + rewrite odd_count_app_single_even_123.
      * exact Hcount.
      * destruct (Z.odd cur) eqn:Hodd; [|reflexivity].
        rewrite Zeven.Zeven_odd_bool, Hodd in Heven.
        discriminate.
    + split; lia.
Qed.

Lemma collatz_final_count_from_state_123 : forall n count,
  collatz_count_state_123 n 1 count ->
  collatz_final_count_123 n count.
Proof.
  intros n count Hstate.
  destruct Hstate as [prefix [suffix [Hseq [Hsafe Hrest]]]].
  destruct Hrest as [_ [_ [_ [Hcount Hcbounds]]]].
  pose proof (suffix_empty_at_one_123 n prefix suffix Hseq) as Hsuffix.
  subst suffix.
  exists (prefix ++ [1]).
  split; [exact Hseq|].
  split; [exact Hsafe|].
  split.
  - rewrite odd_count_app_single_odd_123 by reflexivity.
    lia.
  - exact Hcbounds.
Qed.

Lemma collatz_output_state_init_123 : forall n count,
  problem_123_pre_z n ->
  collatz_safe_123 n ->
  collatz_final_count_123 n count ->
  collatz_output_state_123 n count n [1].
Proof.
  intros n count _ _ Hfinal.
  pose proof Hfinal as Hfinal_full.
  destruct Hfinal as [seq [Hseq [Hsafe [Hfinal_count_eq Hcbounds]]]].
  destruct seq as [|h t].
  - destruct Hseq as [Hne _]. contradiction Hne; reflexivity.
  - pose proof Hseq as Hseq_full.
    destruct Hseq as [Hne [Hhd [Hlast Hsteps]]].
    simpl in Hhd. subst h.
    pose proof Hfinal_count_eq as Hcnt_eq_keep.
    destruct Hsafe as [Hforall Hlen].
    inversion Hforall as [|? ? Hh _]; subst.
    destruct Hh as [[Hn_pos Hn_lt] Hn_step].
    exists [], t.
    split; [exact Hseq_full|].
    split; [split; [exact Hforall | exact Hlen]|].
    split; [exact Hfinal_full|].
    split; [exact Hcnt_eq_keep|].
    split; [exact Hn_pos|].
    split; [exact Hn_lt|].
    split; [exact Hn_step|].
    reflexivity.
Qed.

Lemma collatz_output_state_odd_step_123 : forall n count cur output,
  0 < cur ->
  cur mod 2 = 1 ->
  cur <> 1 ->
  collatz_output_state_123 n count cur output ->
  collatz_output_state_123 n count (3 * cur + 1) (output ++ [cur]).
Proof.
  intros n count cur output Hpos Hmod Hne Hstate.
  destruct Hstate as [prefix [suffix [Hseq [Hsafe [Hfinal [Hcount Hrest]]]]]].
  destruct Hrest as [Hcur_pos [Hcur_lt [Hcur_step_bound Hout]]].
  destruct suffix as [|next rest].
  - destruct Hseq as [_ [_ [Hlast _]]].
    rewrite last_app_single_123 in Hlast.
    lia.
  - pose proof Hseq as Hseq_full.
    pose proof Hsafe as Hsafe_full.
    destruct Hseq as [Hnonempty [Hhd [Hlast Hsteps]]].
    destruct Hsafe as [Hforall Hlen].
    pose proof (collatz_pair_after_prefix_123 prefix cur next rest Hsteps)
      as Hpair.
    unfold collatz_step in Hpair.
    destruct Hpair as [_ Hnext].
    rewrite z_even_false_of_mod_one_123 in Hnext by exact Hmod.
    subst next.
    exists (prefix ++ [cur]), rest.
    rewrite <- app_assoc. simpl.
    split; [exact Hseq_full|].
    split; [exact Hsafe_full|].
    split; [exact Hfinal|].
    split; [exact Hcount|].
    rewrite Forall_forall in Hforall.
    assert (Hnext_bounds :
      0 < 3 * cur + 1 < INT_MAX /\ 3 * (3 * cur + 1) + 1 <= INT_MAX).
    { apply Hforall.
      apply in_or_app. right. simpl. auto. }
    destruct Hnext_bounds as [[Hnext_pos Hnext_lt] Hnext_step].
    split; [exact Hnext_pos|].
    split; [exact Hnext_lt|].
    split; [exact Hnext_step|].
    subst output.
      unfold odd_filter_123.
      rewrite filter_app. simpl.
      rewrite z_odd_of_mod_one_123 by exact Hmod.
      reflexivity.
Qed.

Lemma collatz_output_state_even_step_123 : forall n count cur output,
  0 < cur ->
  cur mod 2 <> 1 ->
  cur <> 1 ->
  collatz_output_state_123 n count cur output ->
  collatz_output_state_123 n count (cur ÷ 2) output.
Proof.
  intros n count cur output Hpos Hmod Hne Hstate.
  destruct Hstate as [prefix [suffix [Hseq [Hsafe [Hfinal [Hcount Hrest]]]]]].
  destruct Hrest as [Hcur_pos [Hcur_lt [Hcur_step_bound Hout]]].
  destruct suffix as [|next rest].
  - destruct Hseq as [_ [_ [Hlast _]]].
    rewrite last_app_single_123 in Hlast.
    lia.
  - pose proof Hseq as Hseq_full.
    pose proof Hsafe as Hsafe_full.
    destruct Hseq as [Hnonempty [Hhd [Hlast Hsteps]]].
    destruct Hsafe as [Hforall Hlen].
    pose proof (collatz_pair_after_prefix_123 prefix cur next rest Hsteps)
      as Hpair.
    unfold collatz_step in Hpair.
    destruct Hpair as [_ Hnext].
    pose proof (z_even_true_of_not_mod_one_123 _ Hpos Hmod) as Heven.
    rewrite Heven in Hnext.
    rewrite <- (Z.quot_div_nonneg cur 2) in Hnext by lia.
    subst next.
    exists (prefix ++ [cur]), rest.
    rewrite <- app_assoc. simpl.
    split; [exact Hseq_full|].
    split; [exact Hsafe_full|].
    split; [exact Hfinal|].
    split; [exact Hcount|].
    rewrite Forall_forall in Hforall.
    assert (Hnext_bounds :
      0 < cur ÷ 2 < INT_MAX /\ 3 * (cur ÷ 2) + 1 <= INT_MAX).
    { apply Hforall.
      apply in_or_app. right. simpl. auto. }
    destruct Hnext_bounds as [[Hnext_pos Hnext_lt] Hnext_step].
    split; [exact Hnext_pos|].
    split; [exact Hnext_lt|].
    split; [exact Hnext_step|].
    subst output.
    unfold odd_filter_123, odd_z_123.
    rewrite filter_app. simpl.
    destruct (Z.odd cur) eqn:Hodd.
    { rewrite Zeven.Zeven_odd_bool, Hodd in Heven. discriminate. }
    { rewrite app_nil_r. reflexivity. }
Qed.

Lemma collatz_output_odd_room_123 : forall n count cur output,
  cur <> 1 ->
  cur mod 2 = 1 ->
  collatz_output_state_123 n count cur output ->
  Zlength output + 1 <= count.
Proof.
  intros n count cur output Hne Hmod Hstate.
  destruct Hstate as [prefix [suffix [Hseq [_ [_ [Hcount Hrest]]]]]].
  destruct Hrest as [_ [_ [_ Hout]]].
  subst output.
  destruct suffix as [|next rest].
  - destruct Hseq as [_ [_ [Hlast _]]].
    rewrite last_app_single_123 in Hlast.
    lia.
  - destruct Hseq as [_ [_ [Hlast _]]].
    rewrite Hcount.
    rewrite Zlength_cons, Zlength_odd_filter_123.
    rewrite odd_count_app_123.
    rewrite odd_count_cons_123.
    rewrite z_odd_of_mod_one_123 by exact Hmod.
    pose proof (odd_count_pos_of_last_one_123 (next :: rest)) as Hsuffix_odd.
    simpl in Hsuffix_odd.
    rewrite last_after_prefix_123 in Hlast.
    specialize (Hsuffix_odd ltac:(discriminate) Hlast).
    lia.
Qed.

Lemma collatz_output_final_size_123 : forall n count output,
  collatz_output_state_123 n count 1 output ->
  Zlength output = count.
Proof.
  intros n count output Hstate.
  destruct Hstate as [prefix [suffix [Hseq [_ [_ [Hcount Hrest]]]]]].
  destruct Hrest as [_ [_ [_ Hout]]].
  pose proof (suffix_empty_at_one_123 n prefix suffix Hseq) as Hsuffix.
  subst suffix output.
  rewrite Hcount.
  rewrite Zlength_cons, Zlength_odd_filter_123.
  rewrite odd_count_app_single_odd_123 by reflexivity.
  lia.
Qed.

Lemma collatz_output_final_spec_123 : forall n count output sorted,
  collatz_output_state_123 n count 1 output ->
  sorted_int_list_by 1 sorted ->
  Permutation output sorted ->
  problem_123_spec_z n sorted.
Proof.
  intros n count output sorted Hstate Hsorted Hperm.
  destruct Hstate as [prefix [suffix [Hseq [_ [_ [_ Hrest]]]]]].
  destruct Hrest as [_ [_ [_ Hout]]].
  pose proof (suffix_empty_at_one_123 n prefix suffix Hseq) as Hsuffix.
  subst suffix output.
  unfold problem_123_spec_z, problem_123_spec.
  exists (prefix ++ [1]).
  split; [exact Hseq|].
  split.
  - unfold odd_filter_123 in *.
    eapply Permutation_trans.
    + apply Permutation_sym. exact Hperm.
    + simpl.
    rewrite filter_app. simpl.
    apply Permutation_cons_append.
  - unfold sorted_int_list_by in Hsorted.
    simpl in Hsorted.
    exact Hsorted.
Qed.
