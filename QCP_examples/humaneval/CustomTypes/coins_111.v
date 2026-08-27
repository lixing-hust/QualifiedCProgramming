Load "../spec/111".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Export string_bridge.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_111_pre_z (input : list Z) : Prop :=
  problem_111_pre (string_of_list_z input).

Definition histogram_pairs_111 (keys values : list Z) : list (ascii * nat) :=
  combine (map ascii_of_z keys) (map Z.to_nat values).

Definition problem_111_spec_z
    (input keys values : list Z) : Prop :=
  problem_111_spec
    (string_of_list_z input)
    (histogram_pairs_111 keys values).

Definition histogram_zero_counts_111 : list Z := zeros 256.

Definition histogram_bump_111 (counts : list Z) (ch : Z) : list Z :=
  replace_Znth ch (Znth ch counts 0 + 1) counts.

Definition histogram_step_111
    (ch : Z) (state : list Z * Z) : list Z * Z :=
  let '(counts, current_max) := state in
  if Z.eqb ch 32 then (counts, current_max)
  else
    let next_count := Znth ch counts 0 + 1 in
    (histogram_bump_111 counts ch, Z.max current_max next_count).

Fixpoint histogram_scan_111
    (input : list Z) (state : list Z * Z) : list Z * Z :=
  match input with
  | [] => state
  | ch :: rest => histogram_scan_111 rest (histogram_step_111 ch state)
  end.

Definition histogram_prefix_111 (input : list Z) (i : Z) : list Z :=
  sublist 0 i input.

Definition histogram_scan_state_111
    (input : list Z) (i : Z) (counts : list Z) (current_max : Z) : Prop :=
  histogram_scan_111
    (histogram_prefix_111 input i)
    (histogram_zero_counts_111, 0) = (counts, current_max).

Definition histogram_counts_bounded_111 (counts : list Z) (processed : Z) : Prop :=
  forall ch, 0 <= ch < Zlength counts -> 0 <= Znth ch counts 0 <= processed.

Definition histogram_selected_111
    (counts : list Z) (current_max ch : Z) : bool :=
  andb (Z.eqb (Znth ch counts 0) current_max) (Z.ltb 0 current_max).

Definition histogram_indices_111 (upto : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat upto)).

Definition histogram_output_keys_111
    (counts : list Z) (current_max upto : Z) : list Z :=
  filter (fun ch => histogram_selected_111 counts current_max ch)
    (histogram_indices_111 upto).

Definition histogram_output_values_111
  (counts : list Z) (current_max upto : Z) : list Z :=
  repeat current_max
    (List.length (histogram_output_keys_111 counts current_max upto)).

Definition histogram_output_state_111
    (counts : list Z) (current_max upto : Z)
    (keys values : list Z) : Prop :=
  keys = histogram_output_keys_111 counts current_max upto /\
  values = histogram_output_values_111 counts current_max upto.

Lemma histogram_zero_counts_length_111 :
  Zlength histogram_zero_counts_111 = 256.
Proof.
  unfold histogram_zero_counts_111, zeros.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.

Lemma histogram_scan_state_init_111 : forall input,
  histogram_scan_state_111 input 0 histogram_zero_counts_111 0.
Proof.
  intros input.
  unfold histogram_scan_state_111, histogram_prefix_111.
  unfold sublist.
  simpl.
  reflexivity.
Qed.

Lemma histogram_output_state_init_111 : forall counts current_max,
  histogram_output_state_111 counts current_max 0 [] [].
Proof.
  intros counts current_max.
  unfold histogram_output_state_111, histogram_output_keys_111,
    histogram_output_values_111, histogram_indices_111.
  simpl.
  auto.
Qed.

Lemma histogram_scan_app_111 : forall a b state,
  histogram_scan_111 (a ++ b) state =
  histogram_scan_111 b (histogram_scan_111 a state).
Proof.
  induction a as [|x xs IH]; intros b state; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma histogram_prefix_snoc_111 : forall input i,
  0 <= i < Zlength input ->
  histogram_prefix_111 input (i + 1) =
  histogram_prefix_111 input i ++ [Znth i input 0].
Proof.
  intros input i Hi.
  unfold histogram_prefix_111.
  pose proof (@sublist_split Z 0 (i + 1) i input ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite Hsplit.
  rewrite (@sublist_single Z 0 i input) by lia.
  reflexivity.
Qed.

Lemma histogram_scan_state_step_nonspace_111 : forall input i counts current_max ch,
  0 <= i < Zlength input ->
  ch = Znth i input 0 ->
  ch <> 32 ->
  histogram_scan_state_111 input i counts current_max ->
  histogram_scan_state_111 input (i + 1)
    (histogram_bump_111 counts ch)
    (Z.max current_max (Znth ch counts 0 + 1)).
Proof.
  intros input i counts current_max ch Hi Hch Hspace Hstate.
  unfold histogram_scan_state_111 in *.
  rewrite histogram_prefix_snoc_111 by exact Hi.
  rewrite histogram_scan_app_111.
  simpl.
  rewrite <- Hch.
  rewrite Hstate.
  unfold histogram_step_111.
  destruct (Z.eqb ch 32) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma histogram_scan_state_step_nonspace_gt_111 : forall input i counts current_max ch,
  0 <= i < Zlength input ->
  ch = Znth i input 0 ->
  ch <> 32 ->
  Znth ch counts 0 + 1 > current_max ->
  histogram_scan_state_111 input i counts current_max ->
  histogram_scan_state_111 input (i + 1)
    (replace_Znth ch (Znth ch counts 0 + 1) counts)
    (Znth ch counts 0 + 1).
Proof.
  intros input i counts current_max ch Hi Hch Hspace Hgt Hstate.
  pose proof (histogram_scan_state_step_nonspace_111
    input i counts current_max ch Hi Hch Hspace Hstate) as Hstep.
  unfold histogram_bump_111 in Hstep.
  rewrite Z.max_r in Hstep by lia.
  exact Hstep.
Qed.

Lemma histogram_scan_state_step_nonspace_le_111 : forall input i counts current_max ch,
  0 <= i < Zlength input ->
  ch = Znth i input 0 ->
  ch <> 32 ->
  Znth ch counts 0 + 1 <= current_max ->
  histogram_scan_state_111 input i counts current_max ->
  histogram_scan_state_111 input (i + 1)
    (replace_Znth ch (Znth ch counts 0 + 1) counts)
    current_max.
Proof.
  intros input i counts current_max ch Hi Hch Hspace Hle Hstate.
  pose proof (histogram_scan_state_step_nonspace_111
    input i counts current_max ch Hi Hch Hspace Hstate) as Hstep.
  unfold histogram_bump_111 in Hstep.
  rewrite Z.max_l in Hstep by lia.
  exact Hstep.
Qed.

Lemma histogram_scan_state_step_space_111 : forall input i counts current_max,
  0 <= i < Zlength input ->
  Znth i input 0 = 32 ->
  histogram_scan_state_111 input i counts current_max ->
  histogram_scan_state_111 input (i + 1) counts current_max.
Proof.
  intros input i counts current_max Hi Hspace Hstate.
  unfold histogram_scan_state_111 in *.
  rewrite histogram_prefix_snoc_111 by exact Hi.
  rewrite histogram_scan_app_111.
  simpl.
  rewrite Hstate.
  unfold histogram_step_111.
  rewrite Hspace, Z.eqb_refl.
  reflexivity.
Qed.

Lemma histogram_zero_counts_bounded_111 :
  histogram_counts_bounded_111 histogram_zero_counts_111 0.
Proof.
  intros ch Hch.
  unfold histogram_zero_counts_111, zeros.
  rewrite Znth_repeat by (rewrite Zlength_correct, repeat_length in Hch; lia).
  lia.
Qed.

Lemma histogram_counts_bounded_weaken_111 : forall counts processed,
  histogram_counts_bounded_111 counts processed ->
  histogram_counts_bounded_111 counts (processed + 1).
Proof.
  intros counts processed Hbound ch Hch.
  specialize (Hbound ch Hch).
  lia.
Qed.

Lemma histogram_counts_bounded_bump_111 : forall counts processed ch,
  histogram_counts_bounded_111 counts processed ->
  0 <= ch < Zlength counts ->
  histogram_counts_bounded_111
    (replace_Znth ch (Znth ch counts 0 + 1) counts)
    (processed + 1).
Proof.
  intros counts processed ch Hbound Hch k Hk.
  rewrite Zlength_replace_Znth in Hk.
  destruct (Z.eq_dec k ch) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by exact Hch.
    specialize (Hbound ch Hch).
    lia.
  - rewrite Znth_replace_Znth_Diff by (try exact Hch; try exact Hk; lia).
    specialize (Hbound k Hk).
    lia.
Qed.

Lemma histogram_counts_bounded_at_111 : forall counts processed ch,
  histogram_counts_bounded_111 counts processed ->
  0 <= ch < Zlength counts ->
  0 <= Znth ch counts 0 <= processed.
Proof.
  intros counts processed ch Hbound Hch.
  apply Hbound; exact Hch.
Qed.

Lemma histogram_Znth_c_string_inside_111 : forall input i,
  0 <= i < Zlength input ->
  Znth i (input ++ [0]) 0 = Znth i input 0.
Proof.
  intros input i Hi.
  apply app_Znth1.
  exact Hi.
Qed.

Lemma histogram_Znth_c_string_end_111 : forall input,
  Znth (Zlength input) (input ++ [0]) 0 = 0.
Proof.
  intros input.
  rewrite app_Znth2 by lia.
  replace (Zlength input - Zlength input) with 0 by lia.
  reflexivity.
Qed.

Lemma histogram_c_string_nonzero_inside_111 : forall input i,
  valid_string input ->
  0 <= i < Zlength input ->
  Znth i (input ++ [0]) 0 <> 0.
Proof.
  intros input i Hvalid Hi.
  rewrite histogram_Znth_c_string_inside_111 by exact Hi.
  destruct Hvalid as [_ Hnozero].
  apply Hnozero.
  exact Hi.
Qed.

Lemma histogram_c_string_nonzero_index_111 : forall input n i,
  Zlength input = n ->
  valid_string input ->
  0 <= i <= n ->
  Znth i (input ++ [0]) 0 <> 0 ->
  i < n.
Proof.
  intros input n i Hlen Hvalid Hi Hnonzero.
  destruct (Z.eq_dec i n); [subst i | lia].
  rewrite <- Hlen in Hnonzero.
  rewrite histogram_Znth_c_string_end_111 in Hnonzero.
  contradiction.
Qed.

Lemma histogram_indices_snoc_111 : forall upto,
  0 <= upto ->
  histogram_indices_111 (upto + 1) = histogram_indices_111 upto ++ [upto].
Proof.
  intros upto Hupto.
  unfold histogram_indices_111.
  assert (Hnat : Z.to_nat (upto + 1) = S (Z.to_nat upto)) by lia.
  rewrite Hnat, seq_S, map_app.
  simpl.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma repeat_snoc_111 : forall (x : Z) n,
  repeat x (S n) = repeat x n ++ [x].
Proof.
  intros x n.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma histogram_output_keys_step_selected_111 : forall counts current_max upto,
  0 <= upto ->
  Znth upto counts 0 = current_max ->
  current_max > 0 ->
  histogram_output_keys_111 counts current_max (upto + 1) =
  histogram_output_keys_111 counts current_max upto ++ [upto].
Proof.
  intros counts current_max upto Hupto Hcount Hmax.
  unfold histogram_output_keys_111.
  rewrite histogram_indices_snoc_111 by exact Hupto.
  rewrite filter_app.
  simpl.
  unfold histogram_selected_111.
  rewrite Hcount, Z.eqb_refl.
  assert (Z.ltb 0 current_max = true) by (apply Z.ltb_lt; lia).
  rewrite H.
  reflexivity.
Qed.

Lemma histogram_output_keys_step_not_count_111 : forall counts current_max upto,
  0 <= upto ->
  Znth upto counts 0 <> current_max ->
  histogram_output_keys_111 counts current_max (upto + 1) =
  histogram_output_keys_111 counts current_max upto.
Proof.
  intros counts current_max upto Hupto Hcount.
  unfold histogram_output_keys_111.
  rewrite histogram_indices_snoc_111 by exact Hupto.
  rewrite filter_app.
  simpl.
  unfold histogram_selected_111.
  assert (Z.eqb (Znth upto counts 0) current_max = false)
    by (apply Z.eqb_neq; exact Hcount).
  rewrite H.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma histogram_output_keys_step_nonpositive_111 : forall counts current_max upto,
  0 <= upto ->
  current_max <= 0 ->
  histogram_output_keys_111 counts current_max (upto + 1) =
  histogram_output_keys_111 counts current_max upto.
Proof.
  intros counts current_max upto Hupto Hmax.
  unfold histogram_output_keys_111.
  rewrite histogram_indices_snoc_111 by exact Hupto.
  rewrite filter_app.
  simpl.
  unfold histogram_selected_111.
  assert (Z.ltb 0 current_max = false) by (apply Z.ltb_ge; lia).
  rewrite H, andb_false_r, app_nil_r.
  reflexivity.
Qed.

Lemma histogram_output_state_step_selected_111 : forall counts current_max upto keys values,
  0 <= upto ->
  Znth upto counts 0 = current_max ->
  current_max > 0 ->
  histogram_output_state_111 counts current_max upto keys values ->
  histogram_output_state_111 counts current_max (upto + 1)
    (keys ++ [upto]) (values ++ [Znth upto counts 0]).
Proof.
  intros counts current_max upto keys values Hupto Hcount Hmax [Hkeys Hvalues].
  unfold histogram_output_state_111.
  split.
  - rewrite histogram_output_keys_step_selected_111 by assumption.
    now rewrite Hkeys.
  - unfold histogram_output_values_111 in *.
    rewrite histogram_output_keys_step_selected_111 by assumption.
    rewrite app_length; simpl.
    replace (List.length (histogram_output_keys_111 counts current_max upto) + 1)%nat
      with (S (List.length (histogram_output_keys_111 counts current_max upto))) by lia.
    rewrite repeat_snoc_111.
    rewrite Hcount, Hvalues.
    reflexivity.
Qed.

Lemma histogram_output_state_step_not_count_111 : forall counts current_max upto keys values,
  0 <= upto ->
  Znth upto counts 0 <> current_max ->
  histogram_output_state_111 counts current_max upto keys values ->
  histogram_output_state_111 counts current_max (upto + 1) keys values.
Proof.
  intros counts current_max upto keys values Hupto Hcount [Hkeys Hvalues].
  unfold histogram_output_state_111, histogram_output_values_111 in *.
  rewrite histogram_output_keys_step_not_count_111 by assumption.
  auto.
Qed.

Lemma histogram_output_state_step_nonpositive_111 : forall counts current_max upto keys values,
  0 <= upto ->
  current_max <= 0 ->
  histogram_output_state_111 counts current_max upto keys values ->
  histogram_output_state_111 counts current_max (upto + 1) keys values.
Proof.
  intros counts current_max upto keys values Hupto Hmax [Hkeys Hvalues].
  unfold histogram_output_state_111, histogram_output_values_111 in *.
  rewrite histogram_output_keys_step_nonpositive_111 by assumption.
  auto.
Qed.

Definition histogram_zcount_111 (ch : Z) (input : list Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec input ch).

Definition histogram_chars_range_111 (input : list Z) : Prop :=
  Forall (fun ch => 0 <= ch < 256) input.

Definition histogram_summary_111
    (input counts : list Z) (current_max : Z) : Prop :=
  Zlength counts = 256 /\
  (forall ch, 0 <= ch < 256 ->
    Znth ch counts 0 =
      if Z.eq_dec ch 32 then 0 else histogram_zcount_111 ch input) /\
  (forall ch, 0 <= ch < 256 -> Znth ch counts 0 <= current_max) /\
  0 <= current_max /\
  (current_max = 0 <-> forall ch, In ch input -> ch = 32) /\
  (current_max > 0 -> exists ch,
    0 <= ch < 256 /\ In ch input /\ ch <> 32 /\
    Znth ch counts 0 = current_max).

Lemma histogram_zcount_nonneg_111 : forall ch input,
  0 <= histogram_zcount_111 ch input.
Proof.
  intros ch input.
  unfold histogram_zcount_111.
  lia.
Qed.

Lemma histogram_zcount_snoc_eq_111 : forall input ch,
  histogram_zcount_111 ch (input ++ [ch]) =
  histogram_zcount_111 ch input + 1.
Proof.
  intros input ch.
  unfold histogram_zcount_111.
  rewrite count_occ_app.
  simpl.
  destruct (Z.eq_dec ch ch); [lia | contradiction].
Qed.

Lemma histogram_zcount_snoc_neq_111 : forall input ch other,
  ch <> other ->
  histogram_zcount_111 ch (input ++ [other]) =
  histogram_zcount_111 ch input.
Proof.
  intros input ch other Hneq.
  unfold histogram_zcount_111.
  rewrite count_occ_app.
  simpl.
  destruct (Z.eq_dec other ch); [congruence | lia].
Qed.

Lemma histogram_summary_empty_111 :
  histogram_summary_111 [] histogram_zero_counts_111 0.
Proof.
  unfold histogram_summary_111.
  split; [exact histogram_zero_counts_length_111 |].
  split.
  - intros ch Hch.
    unfold histogram_zero_counts_111, zeros.
    rewrite Znth_repeat by (rewrite Zlength_correct, repeat_length; lia).
    destruct (Z.eq_dec ch 32); reflexivity.
  - split.
    + intros ch Hch.
      unfold histogram_zero_counts_111, zeros.
      rewrite Znth_repeat by (rewrite Zlength_correct, repeat_length; lia).
      lia.
    + split; [lia |].
      split.
      * split.
        -- intros _ x Hin. contradiction.
        -- intros _. reflexivity.
      * lia.
Qed.

Lemma histogram_summary_step_space_111 : forall input counts current_max,
  histogram_summary_111 input counts current_max ->
  histogram_summary_111 (input ++ [32]) counts current_max.
Proof.
  intros input counts current_max
    (Hlen & Hcounts & Hupper & Hmax & Hzero & Hwitness).
  unfold histogram_summary_111.
  split; [exact Hlen |].
  split.
  - intros ch Hch.
    specialize (Hcounts ch Hch).
    destruct (Z.eq_dec ch 32) as [-> | Hneq].
    + exact Hcounts.
    + rewrite Hcounts.
      rewrite histogram_zcount_snoc_neq_111 by congruence.
      reflexivity.
  - split; [exact Hupper |].
    split; [exact Hmax |].
    split.
    + split.
      * intros Hm ch Hin.
        apply in_app_or in Hin.
        destruct Hin as [Hin | Hin].
        -- apply (proj1 Hzero Hm ch Hin).
        -- simpl in Hin. destruct Hin as [-> | []]. reflexivity.
      * intros Hall.
        apply (proj2 Hzero).
        intros ch Hin.
        apply Hall.
        apply in_or_app. left. exact Hin.
    + intros Hpos.
      destruct (Hwitness Hpos) as (ch & Hrange & Hin & Hneq & Hcount).
      exists ch.
      split; [exact Hrange |].
      split.
      * apply in_or_app. left. exact Hin.
      * split; assumption.
Qed.

Lemma histogram_summary_step_nonspace_111 : forall input counts current_max ch,
  histogram_summary_111 input counts current_max ->
  0 <= ch < 256 ->
  ch <> 32 ->
  histogram_summary_111 (input ++ [ch])
    (replace_Znth ch (Znth ch counts 0 + 1) counts)
    (Z.max current_max (Znth ch counts 0 + 1)).
Proof.
  intros input counts current_max ch
    (Hlen & Hcounts & Hupper & Hmax & Hzero & Hwitness) Hch Hspace.
  assert (Hold_nonneg : 0 <= Znth ch counts 0).
  {
    rewrite Hcounts by exact Hch.
    destruct (Z.eq_dec ch 32); [contradiction |].
    apply histogram_zcount_nonneg_111.
  }
  unfold histogram_summary_111.
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + intros k Hk.
    destruct (Z.eq_dec k ch) as [-> | Hneq].
      * rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hch).
        rewrite Hcounts by exact Hch.
        destruct (Z.eq_dec ch 32); [contradiction |].
        rewrite histogram_zcount_snoc_eq_111.
        reflexivity.
      * rewrite Znth_replace_Znth_Diff
          by (try rewrite Hlen; try exact Hch; try exact Hk; try congruence).
        rewrite Hcounts by exact Hk.
        destruct (Z.eq_dec k 32) as [-> | Hkspace].
        -- reflexivity.
        -- rewrite histogram_zcount_snoc_neq_111 by congruence.
           reflexivity.
    + split.
      * intros k Hk.
        destruct (Z.eq_dec k ch) as [-> | Hneq].
        -- rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hch).
           apply Z.le_max_r.
        -- rewrite Znth_replace_Znth_Diff
             by (try rewrite Hlen; try exact Hch; try exact Hk; try congruence).
           eapply Z.le_trans; [apply Hupper; exact Hk | apply Z.le_max_l].
      * split.
        -- pose proof (Z.le_max_l current_max (Znth ch counts 0 + 1)). lia.
        -- split.
           ++ split.
              ** intros Hzero_new.
                 assert (Hnext : Znth ch counts 0 + 1 <= 0).
                 { eapply Z.le_trans; [apply Z.le_max_r | lia]. }
                 lia.
              ** intros Hall.
                 assert (Hin : In ch (input ++ [ch])).
                 { apply in_or_app. right. simpl. auto. }
                 specialize (Hall ch Hin).
                 contradiction.
           ++ intros Hpositive.
              destruct (Z_lt_ge_dec current_max (Znth ch counts 0 + 1))
                as [Hnew | Hold].
              ** exists ch.
                 split; [exact Hch |].
                 split.
                 --- apply in_or_app. right. simpl. auto.
                 --- split; [exact Hspace |].
                     rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hch).
                     rewrite Z.max_r by lia.
                     reflexivity.
              ** assert (Hmax_eq :
                    Z.max current_max (Znth ch counts 0 + 1) = current_max)
                    by (apply Z.max_l; lia).
                 assert (Hmax_pos : current_max > 0)
                   by (rewrite Hmax_eq in Hpositive; exact Hpositive).
                 destruct (Hwitness Hmax_pos)
                   as (w & Hwrange & Hin & Hwspace & Hwcount).
                 exists w.
                 split; [exact Hwrange |].
                 split.
                 --- apply in_or_app. left. exact Hin.
                 --- split; [exact Hwspace |].
                     destruct (Z.eq_dec w ch) as [-> | Hneq].
                     +++ rewrite Znth_replace_Znth_Same
                           by (rewrite Hlen; exact Hch).
                         rewrite Hmax_eq.
                         lia.
                     +++ rewrite Znth_replace_Znth_Diff
                           by (try rewrite Hlen; try exact Hch;
                               try exact Hwrange; try congruence).
                         rewrite Hmax_eq.
                         exact Hwcount.
  Unshelve.
  exact 0.
Qed.

Lemma histogram_scan_final_summary_111 : forall input,
  histogram_chars_range_111 input ->
  histogram_summary_111 input
    (fst (histogram_scan_111 input (histogram_zero_counts_111, 0)))
    (snd (histogram_scan_111 input (histogram_zero_counts_111, 0))).
Proof.
  intros input.
  induction input using rev_ind; intros Hrange.
  - simpl. apply histogram_summary_empty_111.
  - apply Forall_app in Hrange.
    destruct Hrange as [Hprefix Hlast].
    inversion Hlast as [|y ys Hx Hnil]; subst.
    specialize (IHinput Hprefix).
    rewrite histogram_scan_app_111.
    remember (histogram_scan_111 input (histogram_zero_counts_111, 0))
      as state eqn:Hstate.
    destruct state as [counts current_max].
    simpl in *.
    unfold histogram_step_111.
    destruct (Z.eq_dec x 32) as [-> | Hspace].
    + rewrite Z.eqb_refl.
      apply histogram_summary_step_space_111.
      exact IHinput.
    + assert (Z.eqb x 32 = false) by (apply Z.eqb_neq; exact Hspace).
      rewrite H.
      unfold histogram_bump_111.
      eapply histogram_summary_step_nonspace_111.
      * exact IHinput.
      * exact Hx.
      * exact Hspace.
Qed.

Lemma histogram_prefix_full_111 : forall input,
  histogram_prefix_111 input (Zlength input) = input.
Proof.
  intros input.
  unfold histogram_prefix_111.
  apply sublist_self.
  reflexivity.
Qed.

Lemma histogram_scan_state_final_summary_111 : forall input counts current_max,
  histogram_chars_range_111 input ->
  histogram_scan_state_111 input (Zlength input) counts current_max ->
  histogram_summary_111 input counts current_max.
Proof.
  intros input counts current_max Hrange Hstate.
  unfold histogram_scan_state_111 in Hstate.
  rewrite histogram_prefix_full_111 in Hstate.
  pose proof (histogram_scan_final_summary_111 input Hrange) as Hsummary.
  rewrite Hstate in Hsummary.
  exact Hsummary.
Qed.

Definition histogram_filter_spaces_z_111 (input : list Z) : list Z :=
  filter (fun ch => negb (Z.eqb ch 32)) input.

Lemma ascii_of_z_space_iff_111 : forall ch,
  0 <= ch < 256 ->
  ascii_of_z ch = " "%char <-> ch = 32.
Proof.
  intros ch Hch.
  split.
  - intros Heq.
    apply (f_equal nat_of_ascii) in Heq.
    rewrite nat_of_ascii_ascii_of_z in Heq by exact Hch.
    change (Z.to_nat ch = 32%nat) in Heq.
    lia.
  - intros ->. reflexivity.
Qed.

Lemma ascii_of_z_injective_111 : forall x y,
  0 <= x < 256 ->
  0 <= y < 256 ->
  ascii_of_z x = ascii_of_z y ->
  x = y.
Proof.
  intros x y Hx Hy Heq.
  apply (f_equal nat_of_ascii) in Heq.
  rewrite !nat_of_ascii_ascii_of_z in Heq by assumption.
  lia.
Qed.

Lemma histogram_filter_spaces_bridge_111 : forall input,
  histogram_chars_range_111 input ->
  filter_spaces (map ascii_of_z input) =
  map ascii_of_z (histogram_filter_spaces_z_111 input).
Proof.
  intros input Hrange.
  induction Hrange as [|ch input Hch Hrange IH]; simpl.
  - reflexivity.
  - unfold histogram_filter_spaces_z_111 in *.
    simpl.
    destruct (Z.eq_dec ch 32) as [-> | Hspace].
    + simpl. exact IH.
    + assert (Hascii : ascii_of_z ch <> " "%char).
      { intros Heq. apply (proj1 (ascii_of_z_space_iff_111 ch Hch)) in Heq.
        contradiction. }
      destruct (ascii_dec (ascii_of_z ch) " "%char); [contradiction |].
      assert (Z.eqb ch 32 = false) by (apply Z.eqb_neq; exact Hspace).
      rewrite H. simpl. f_equal. exact IH.
Qed.

Lemma histogram_filter_spaces_range_111 : forall input,
  histogram_chars_range_111 input ->
  histogram_chars_range_111 (histogram_filter_spaces_z_111 input).
Proof.
  intros input Hrange.
  unfold histogram_filter_spaces_z_111.
  induction Hrange as [|ch input Hch Hrange IH]; simpl.
  - constructor.
  - destruct (negb (ch =? 32)); simpl.
    + constructor; assumption.
    + exact IH.
Qed.

Lemma histogram_filter_spaces_nonspace_111 : forall input ch,
  In ch (histogram_filter_spaces_z_111 input) ->
  ch <> 32.
Proof.
  intros input ch Hin.
  unfold histogram_filter_spaces_z_111 in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hkeep].
  apply Bool.negb_true_iff in Hkeep.
  apply Z.eqb_neq in Hkeep.
  exact Hkeep.
Qed.

Lemma histogram_zcount_filter_111 : forall input ch,
  ch <> 32 ->
  histogram_zcount_111 ch (histogram_filter_spaces_z_111 input) =
  histogram_zcount_111 ch input.
Proof.
  intros input ch Hspace.
  induction input as [|x xs IH].
  - reflexivity.
  - unfold histogram_filter_spaces_z_111 in *.
    simpl.
    destruct (Z.eq_dec x 32) as [-> | Hxspace].
    + rewrite Z.eqb_refl. simpl.
      unfold histogram_zcount_111 in *.
      rewrite count_occ_cons_neq by congruence.
      exact IH.
    + assert (Z.eqb x 32 = false) by (apply Z.eqb_neq; exact Hxspace).
      rewrite H. simpl.
      unfold histogram_zcount_111 in *.
      destruct (Z.eq_dec x ch) as [Heq | Hneq].
      * rewrite !count_occ_cons_eq by exact Heq.
        lia.
      * rewrite !count_occ_cons_neq by exact Hneq.
        exact IH.
Qed.

Lemma histogram_count_ascii_map_111 : forall input ch,
  histogram_chars_range_111 input ->
  0 <= ch < 256 ->
  count_occ ascii_dec (map ascii_of_z input) (ascii_of_z ch) =
  count_occ Z.eq_dec input ch.
Proof.
  intros input ch Hrange Hch.
  induction Hrange as [|x xs Hx Hrange IH]; simpl.
  - reflexivity.
  - destruct (Z.eq_dec x ch) as [-> | Hneq].
    + destruct (ascii_dec (ascii_of_z ch) (ascii_of_z ch));
        [f_equal; exact IH | contradiction].
    + assert (Hascii : ascii_of_z x <> ascii_of_z ch).
      { intros Heq. apply Hneq. eapply ascii_of_z_injective_111; eauto. }
      destruct (ascii_dec (ascii_of_z x) (ascii_of_z ch));
        [contradiction | exact IH].
Qed.

Lemma histogram_indices_In_111 : forall upto ch,
  0 <= upto ->
  (In ch (histogram_indices_111 upto) <-> 0 <= ch < upto).
Proof.
  intros upto ch Hupto.
  unfold histogram_indices_111.
  rewrite in_map_iff.
  split.
  - intros (n & Heq & Hin).
    apply in_seq in Hin.
    subst ch.
    lia.
  - intros Hch.
    exists (Z.to_nat ch).
    split; [lia |].
    apply in_seq.
    lia.
Qed.

Lemma histogram_output_keys_In_111 : forall counts current_max ch,
  In ch (histogram_output_keys_111 counts current_max 256) <->
  0 <= ch < 256 /\ Znth ch counts 0 = current_max /\ current_max > 0.
Proof.
  intros counts current_max ch.
  unfold histogram_output_keys_111.
  rewrite filter_In, histogram_indices_In_111 by lia.
  unfold histogram_selected_111.
  rewrite andb_true_iff, Z.eqb_eq, Z.ltb_lt.
  split; intros (Hrange & Hcount & Hmax);
    repeat split; try assumption; lia.
Qed.

Lemma histogram_pairs_output_111 : forall keys current_max,
  histogram_pairs_111 keys (repeat current_max (List.length keys)) =
  map (fun ch => (ascii_of_z ch, Z.to_nat current_max)) keys.
Proof.
  induction keys as [|ch keys IH]; intros current_max;
    unfold histogram_pairs_111 in *; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma histogram_In_Znth_exists_111 : forall (x : Z) input,
  In x input ->
  exists i, 0 <= i < Zlength input /\ Znth i input 0 = x.
Proof.
  intros x input Hin.
  apply In_nth_error in Hin.
  destruct Hin as (n & Hn).
  exists (Z.of_nat n).
  split.
  - assert ((n < List.length input)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.

Lemma ascii_range_z_chars_range_111 : forall input,
  ascii_range_z input -> histogram_chars_range_111 input.
Proof.
  intros input Hrange.
  unfold histogram_chars_range_111.
  rewrite Forall_forall.
  intros ch Hin.
  destruct (histogram_In_Znth_exists_111 _ _ Hin) as (i & Hi & Hch).
  rewrite <- Hch.
  apply Hrange.
  exact Hi.
Qed.

Lemma histogram_Znth_In_111 : forall (input : list Z) i d,
  0 <= i < Zlength input ->
  In (Znth i input d) input.
Proof.
  intros input i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma problem_111_pre_z_nonzero_111 : forall input i,
  ascii_range_z input ->
  problem_111_pre_z input ->
  0 <= i < Zlength input ->
  Znth i input 0 <> 0.
Proof.
  intros input i Hrange Hpre Hi Hz.
  unfold problem_111_pre_z, problem_111_pre in Hpre.
  rewrite list_ascii_of_string_string_of_list_z in Hpre.
  rewrite Forall_forall in Hpre.
  specialize (Hpre (ascii_of_z (Znth i input 0))).
  assert (Hin : In (ascii_of_z (Znth i input 0)) (map ascii_of_z input)).
  { apply in_map. apply histogram_Znth_In_111. exact Hi. }
  specialize (Hpre Hin).
  rewrite Hz in Hpre.
  destruct Hpre as [Hspace | Hlower].
  - discriminate.
  - rewrite nat_of_ascii_ascii_of_z in Hlower by lia.
    simpl in Hlower. lia.
Qed.

Lemma fold_max_upper_111 : forall values bound,
  Forall (fun value => (value <= bound)%nat) values ->
  (fold_right Nat.max 0 values <= bound)%nat.
Proof.
  intros values bound Hvalues.
  induction Hvalues as [|value values Hvalue Hvalues IH]; simpl; lia.
Qed.

Lemma fold_max_member_111 : forall values value,
  In value values ->
  (value <= fold_right Nat.max 0 values)%nat.
Proof.
  intros values value Hin.
  induction values as [|x xs IH]; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma histogram_get_max_count_111 : forall input counts current_max,
  histogram_chars_range_111 input ->
  histogram_summary_111 input counts current_max ->
  get_max_count
    (map ascii_of_z (histogram_filter_spaces_z_111 input)) =
  Z.to_nat current_max.
Proof.
  intros input counts current_max Hrange Hsummary.
  destruct Hsummary as
    (Hlen & Hcounts & Hupper & Hmax & Hzero & Hwitness).
  set (zletters := histogram_filter_spaces_z_111 input).
  set (letters := map ascii_of_z zletters).
  set (unique_letters := nodup ascii_dec letters).
  assert (Hzrange : histogram_chars_range_111 zletters).
  { subst zletters. apply histogram_filter_spaces_range_111. exact Hrange. }
  assert (Hcount : forall z,
      In z zletters ->
      Z.of_nat (count_char letters (ascii_of_z z)) =
      histogram_zcount_111 z input).
  {
    intros z Hin.
    assert (Hz : 0 <= z < 256).
    { unfold histogram_chars_range_111 in Hzrange.
      rewrite Forall_forall in Hzrange. apply Hzrange. exact Hin. }
    unfold count_char, letters.
    rewrite histogram_count_ascii_map_111 by assumption.
    change (histogram_zcount_111 z zletters = histogram_zcount_111 z input).
    apply histogram_zcount_filter_111.
    subst zletters.
    eapply histogram_filter_spaces_nonspace_111; eauto.
  }
  unfold get_max_count.
  fold unique_letters.
  assert (Hupper_counts :
      Forall (fun value => (value <= Z.to_nat current_max)%nat)
        (map (count_char letters) unique_letters)).
  {
    rewrite Forall_forall.
    intros value Hin.
    apply in_map_iff in Hin.
    destruct Hin as (c & <- & Hcunique).
    apply nodup_In in Hcunique.
    subst unique_letters.
    apply in_map_iff in Hcunique.
    destruct Hcunique as (z & <- & Hzletters).
    assert (Hz : 0 <= z < 256).
    { unfold histogram_chars_range_111 in Hzrange.
      rewrite Forall_forall in Hzrange. apply Hzrange. exact Hzletters. }
    pose proof (Hcount z Hzletters) as Hcz.
    specialize (Hupper z Hz).
    rewrite Hcounts in Hupper by exact Hz.
    assert (z <> 32).
    { subst zletters. eapply histogram_filter_spaces_nonspace_111; eauto. }
    destruct (Z.eq_dec z 32); [contradiction |].
    lia.
  }
  apply Nat.le_antisymm.
  - apply fold_max_upper_111. exact Hupper_counts.
  - destruct zletters as [|first rest] eqn:Hzletters_empty.
    + assert (Hall : forall ch, In ch input -> ch = 32).
      {
        intros ch Hin.
        destruct (Z.eq_dec ch 32); [assumption |].
        exfalso.
        assert (In ch (histogram_filter_spaces_z_111 input)).
        { unfold histogram_filter_spaces_z_111.
          apply filter_In. split; [exact Hin |].
          apply Bool.negb_true_iff, Z.eqb_neq. exact n. }
        change (histogram_filter_spaces_z_111 input = []) in Hzletters_empty.
        rewrite Hzletters_empty in H. contradiction.
      }
      assert (current_max = 0) by (apply (proj2 Hzero); exact Hall).
      subst current_max. simpl. lia.
    + assert (Hmaxpos : current_max > 0).
      {
        assert (Hinfirst : In first zletters) by (rewrite Hzletters_empty; simpl; auto).
        assert (Hfirst_nonspace : first <> 32).
        { subst zletters. eapply histogram_filter_spaces_nonspace_111; eauto. }
        destruct (Z.eq_dec current_max 0) as [Hzero_max | Hneq].
        - pose proof (proj1 Hzero Hzero_max first).
          assert (In first input).
          { subst zletters. unfold histogram_filter_spaces_z_111 in Hinfirst.
            apply filter_In in Hinfirst. tauto. }
          specialize (H H0). contradiction.
        - lia.
      }
      destruct (Hwitness Hmaxpos)
        as (z & Hz & Hzin & Hzspace & Hzcount).
      assert (Hzinletters : In z zletters).
      { subst zletters. unfold histogram_filter_spaces_z_111.
        apply filter_In. split; [exact Hzin |].
        apply Bool.negb_true_iff, Z.eqb_neq. exact Hzspace. }
      rewrite Hzletters_empty in Hzinletters.
      assert (Hascii_unique : In (ascii_of_z z) unique_letters).
      { apply nodup_In. subst unique_letters letters.
        apply in_map. exact Hzinletters. }
      assert (Hraw : histogram_zcount_111 z input = current_max).
      { specialize (Hcounts z Hz).
        destruct (Z.eq_dec z 32); [contradiction | congruence]. }
      assert (Hcountnat :
          count_char letters (ascii_of_z z) = Z.to_nat current_max).
      { apply Nat2Z.inj.
        rewrite Hcount by exact Hzinletters.
        rewrite Hraw, Z2Nat.id by lia.
        reflexivity. }
      apply fold_max_member_111.
      rewrite <- Hcountnat.
      apply in_map. exact Hascii_unique.
Qed.

Lemma histogram_count_char_cell_111 : forall input counts current_max ch,
  histogram_chars_range_111 input ->
  histogram_summary_111 input counts current_max ->
  0 <= ch < 256 ->
  ch <> 32 ->
  Z.of_nat
    (count_char
      (map ascii_of_z (histogram_filter_spaces_z_111 input))
      (ascii_of_z ch)) =
  Znth ch counts 0.
Proof.
  intros input counts current_max ch Hrange Hsummary Hch Hspace.
  destruct Hsummary as (_ & Hcounts & _).
  rewrite histogram_count_ascii_map_111.
  - change (histogram_zcount_111 ch
      (histogram_filter_spaces_z_111 input) = Znth ch counts 0).
    rewrite histogram_zcount_filter_111 by exact Hspace.
    symmetry.
    rewrite Hcounts by exact Hch.
    destruct (Z.eq_dec ch 32); [contradiction | reflexivity].
  - apply histogram_filter_spaces_range_111. exact Hrange.
  - exact Hch.
Qed.

Lemma histogram_output_pairs_state_111 : forall counts current_max keys values,
  histogram_output_state_111 counts current_max 256 keys values ->
  histogram_pairs_111 keys values =
  map (fun ch => (ascii_of_z ch, Z.to_nat current_max))
    (histogram_output_keys_111 counts current_max 256).
Proof.
  intros counts current_max keys values [Hkeys Hvalues].
  subst keys values.
  unfold histogram_output_values_111.
  apply histogram_pairs_output_111.
Qed.

Lemma histogram_spec_bridge_111 : forall input counts current_max keys values,
  histogram_chars_range_111 input ->
  histogram_summary_111 input counts current_max ->
  histogram_output_state_111 counts current_max 256 keys values ->
  problem_111_spec_z input keys values.
Proof.
  intros input counts current_max keys values Hrange Hsummary Houtput.
  pose proof Hsummary as Hsummary_copy.
  destruct Hsummary as
    (Hlen & Hcounts & Hupper & Hmax & Hzero & Hwitness).
  pose proof (histogram_output_pairs_state_111
    counts current_max keys values Houtput) as Hpairs.
  unfold problem_111_spec_z, problem_111_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  rewrite histogram_filter_spaces_bridge_111 by exact Hrange.
  set (zletters := histogram_filter_spaces_z_111 input) in *.
  set (letters := map ascii_of_z zletters) in *.
  set (unique_letters := nodup ascii_dec letters) in *.
  assert (Hzrange : histogram_chars_range_111 zletters).
  { subst zletters. apply histogram_filter_spaces_range_111. exact Hrange. }
  assert (Hmax_count : get_max_count letters = Z.to_nat current_max).
  { subst letters zletters.
    apply histogram_get_max_count_111 with (counts := counts); assumption. }
  destruct unique_letters as [|first rest] eqn:Hunique.
  - assert (Hzletters_nil : zletters = []).
    {
      destruct zletters as [|z zs] eqn:Hz; [reflexivity |].
      exfalso.
      assert (Hin_ascii : In (ascii_of_z z) unique_letters).
      { apply nodup_In. subst unique_letters letters. simpl. auto. }
      rewrite Hunique in Hin_ascii. contradiction.
    }
    assert (Hall_space : forall ch, In ch input -> ch = 32).
    {
      intros ch Hin.
      destruct (Z.eq_dec ch 32); [assumption |].
      exfalso.
      assert (Hin_filter : In ch (histogram_filter_spaces_z_111 input)).
      { unfold histogram_filter_spaces_z_111.
        apply filter_In. split; [exact Hin |].
        apply Bool.negb_true_iff, Z.eqb_neq. exact n. }
      change (histogram_filter_spaces_z_111 input = []) in Hzletters_nil.
      rewrite Hzletters_nil in Hin_filter. contradiction.
    }
    assert (Hmaxzero : current_max = 0).
    { apply (proj2 Hzero). exact Hall_space. }
    assert (Houtkeys_nil :
        histogram_output_keys_111 counts current_max 256 = []).
    {
      destruct (histogram_output_keys_111 counts current_max 256)
        as [|ch rest] eqn:Hout; [reflexivity |].
      exfalso.
      assert (Hin : In ch
          (histogram_output_keys_111 counts current_max 256)).
      { rewrite Hout. simpl. auto. }
      apply histogram_output_keys_In_111 in Hin. lia.
    }
    rewrite Hpairs, Houtkeys_nil.
    reflexivity.
  - assert (Hzletters_nonempty : zletters <> []).
    {
      intros Hz.
      assert (Hletters_nil : letters = []).
      { subst letters. rewrite Hz. reflexivity. }
      assert (Hunique_nil : unique_letters = []).
      { subst unique_letters. rewrite Hletters_nil. reflexivity. }
      rewrite Hunique_nil in Hunique. discriminate.
    }
    assert (Hmaxpos : current_max > 0).
    {
      destruct (Z.eq_dec current_max 0) as [Hm | Hm]; [|lia].
      assert (Hall := proj1 Hzero Hm).
      destruct zletters as [|z zs] eqn:Hz; [contradiction |].
      assert (Hin_z : In z zletters).
      { rewrite Hz. simpl. auto. }
      assert (Hin_input : In z input).
      { subst zletters. unfold histogram_filter_spaces_z_111 in Hin_z.
        apply filter_In in Hin_z. tauto. }
      assert (Hzspace : z <> 32).
      { subst zletters. eapply histogram_filter_spaces_nonspace_111; eauto. }
      specialize (Hall z Hin_input). contradiction.
    }
    rewrite Hmax_count.
    split.
    + intros [c n] Hin.
      rewrite Hpairs in Hin.
      apply in_map_iff in Hin.
      destruct Hin as (ch & Hpair & Hkey).
      inversion Hpair; subst c n; clear Hpair.
      apply histogram_output_keys_In_111 in Hkey.
      destruct Hkey as (Hch & Hcell & _).
      assert (Hspace : ch <> 32).
      { intros ->.
        specialize (Hcounts 32 ltac:(lia)).
        destruct (Z.eq_dec 32 32); [lia | contradiction]. }
      split; [reflexivity |].
      apply Nat2Z.inj.
      subst letters zletters.
      rewrite histogram_count_char_cell_111 with
        (counts := counts) (current_max := current_max)
        by (try exact Hrange; try exact Hsummary_copy; try exact Hch;
            try exact Hspace).
      rewrite Hcell, Z2Nat.id by lia.
      reflexivity.
    + intros c Hcunique Hcountmax.
      assert (Hcunique_full : In c unique_letters).
      { rewrite Hunique. exact Hcunique. }
      apply nodup_In in Hcunique_full.
      subst unique_letters.
      apply in_map_iff in Hcunique_full.
      destruct Hcunique_full as (ch & Hc & Hchletters).
      subst c.
      assert (Hch : 0 <= ch < 256).
      { unfold histogram_chars_range_111 in Hzrange.
        rewrite Forall_forall in Hzrange.
        apply Hzrange. exact Hchletters. }
      assert (Hspace : ch <> 32).
      { subst zletters. eapply histogram_filter_spaces_nonspace_111; eauto. }
      assert (Hcell : Znth ch counts 0 = current_max).
      {
        pose proof (histogram_count_char_cell_111 input counts current_max ch
          Hrange Hsummary_copy Hch Hspace) as Hcell_count.
        unfold letters, zletters in Hcountmax.
        rewrite Hcountmax in Hcell_count.
        rewrite Z2Nat.id in Hcell_count by lia.
        exact (eq_sym Hcell_count).
      }
      rewrite Hpairs.
      apply in_map_iff.
      exists ch.
      split; [reflexivity |].
      apply histogram_output_keys_In_111.
      split; [exact Hch |].
      split; assumption.
Qed.
