Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition WindowUpperBoundValue
    (l : list Z) (lo hi ub : Z) : Prop :=
  0 <= lo /\
  lo < hi /\
  hi <= Zlength l /\
  exists pos,
    lo <= pos < hi /\
    ub = Znth pos l 0 /\
    forall idx, lo <= idx < hi -> Znth idx l 0 <= ub.

Definition WindowMaxValue (l : list Z) (lo hi ans : Z) : Prop :=
  min_value_of_subset Z.le
    (fun ub => WindowUpperBoundValue l lo hi ub)
    (fun ub => ub)
    ans.

Definition SlidingWindowMaximum (l : list Z) (k : Z) (out : list Z) : Prop :=
  1 <= k /\
  k <= Zlength l /\
  Zlength out = Zlength l - k + 1 /\
  forall idx,
    0 <= idx < Zlength out ->
    WindowMaxValue l idx (idx + k) (Znth idx out 0).

Definition SWMOutputPrefix
    (l : list Z) (k out_idx : Z) (out : list Z) : Prop :=
  1 <= k /\
  k <= Zlength l /\
  0 <= out_idx /\
  out_idx <= Zlength l - k + 1 /\
  Zlength out = out_idx /\
  forall idx,
    0 <= idx < out_idx ->
    WindowMaxValue l idx (idx + k) (Znth idx out 0).

Definition SWMQueueEntriesValid
    (l q_l : list Z) (head tail processed k : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    0 <= Znth pos q_l 0 /\
    Znth pos q_l 0 < Zlength l /\
    processed - k <= Znth pos q_l 0 /\
    Znth pos q_l 0 < processed.

Definition SWMQueueEntriesValidAfterDrop
    (l q_l : list Z) (head tail i k : Z) : Prop :=
  forall pos,
    head <= pos < tail ->
    0 <= Znth pos q_l 0 /\
    Znth pos q_l 0 < Zlength l /\
    i - k < Znth pos q_l 0 /\
    Znth pos q_l 0 < i.

Definition SWMQueueIndexIncreasing (q_l : list Z) (head tail : Z) : Prop :=
  forall p q,
    head <= p /\ p < q /\ q < tail ->
    Znth p q_l 0 < Znth q q_l 0.

Definition SWMQueueValueDecreasing
    (l q_l : list Z) (head tail : Z) : Prop :=
  forall p q,
    head <= p /\ p < q /\ q < tail ->
    Znth (Znth p q_l 0) l 0 > Znth (Znth q q_l 0) l 0.

Definition SWMQueueCoversWindow
    (l q_l : list Z) (head tail processed k : Z) : Prop :=
  forall idx,
    0 <= idx ->
    idx < Zlength l ->
    processed - k <= idx < processed ->
    exists pos,
      head <= pos < tail /\
      idx <= Znth pos q_l 0 /\
      Znth pos q_l 0 < processed /\
      Znth idx l 0 <= Znth (Znth pos q_l 0) l 0.

Definition SWMQueueCoversAfterDrop
    (l q_l : list Z) (head tail i k : Z) : Prop :=
  forall idx,
    0 <= idx ->
    idx < Zlength l ->
    i - k < idx < i ->
    exists pos,
      head <= pos < tail /\
      idx <= Znth pos q_l 0 /\
      Znth pos q_l 0 < i /\
      Znth idx l 0 <= Znth (Znth pos q_l 0) l 0.

Definition SWMQueueCoversWithPending
    (l q_l : list Z) (head tail i k : Z) : Prop :=
  forall idx,
    0 <= idx ->
    idx < Zlength l ->
    i - k < idx < i ->
    (exists pos,
      head <= pos < tail /\
      idx <= Znth pos q_l 0 /\
      Znth pos q_l 0 < i /\
      Znth idx l 0 <= Znth (Znth pos q_l 0) l 0) \/
    Znth idx l 0 <= Znth i l 0.

Definition SWMQueueDropLoopState
    (l q_l : list Z) (head tail i k : Z) : Prop :=
  1 <= k /\
  k <= Zlength l /\
  0 <= i /\
  i <= Zlength l /\
  0 <= head /\
  head <= tail /\
  tail <= Zlength q_l /\
  tail <= i /\
  SWMQueueEntriesValid l q_l head tail i k /\
  SWMQueueIndexIncreasing q_l head tail /\
  SWMQueueValueDecreasing l q_l head tail /\
  SWMQueueCoversAfterDrop l q_l head tail i k.

Definition SWMQueueAfterDrop
    (l q_l : list Z) (head tail i k : Z) : Prop :=
  1 <= k /\
  k <= Zlength l /\
  0 <= i /\
  i <= Zlength l /\
  0 <= head /\
  head <= tail /\
  tail <= Zlength q_l /\
  tail <= i /\
  SWMQueueEntriesValidAfterDrop l q_l head tail i k /\
  SWMQueueIndexIncreasing q_l head tail /\
  SWMQueueValueDecreasing l q_l head tail /\
  SWMQueueCoversAfterDrop l q_l head tail i k.

Definition SWMQueuePendingState
    (l q_l : list Z) (head tail i k : Z) : Prop :=
  1 <= k /\
  k <= Zlength l /\
  0 <= i /\
  i < Zlength l /\
  0 <= head /\
  head <= tail /\
  tail <= Zlength q_l /\
  tail <= i /\
  SWMQueueEntriesValidAfterDrop l q_l head tail i k /\
  SWMQueueIndexIncreasing q_l head tail /\
  SWMQueueValueDecreasing l q_l head tail /\
  SWMQueueCoversWithPending l q_l head tail i k.

Definition SWMQueueState
    (l q_l : list Z) (head tail processed k : Z) : Prop :=
  1 <= k /\
  k <= Zlength l /\
  0 <= processed /\
  processed <= Zlength l /\
  0 <= head /\
  head <= tail /\
  tail <= Zlength q_l /\
  tail <= processed /\
  SWMQueueEntriesValid l q_l head tail processed k /\
  SWMQueueIndexIncreasing q_l head tail /\
  SWMQueueValueDecreasing l q_l head tail /\
  SWMQueueCoversWindow l q_l head tail processed k /\
  (head < tail /\ k <= processed ->
      WindowMaxValue l (processed - k) processed
        (Znth (Znth head q_l 0) l 0)).

Require Import Coq.micromega.Lia.

(* Helper lemmas migrated from sliding_window_maximum__vc_proving_subagent_tmp_proof_manual__merged.v. *)

Lemma SWMQueueAfterDrop_to_PendingState :
  forall (l q_l : list Z) (head tail i k : Z),
    SWMQueueAfterDrop l q_l head tail i k ->
    i < Zlength l ->
    SWMQueuePendingState l q_l head tail i k.
Proof.
  intros l q_l head tail i k Hdrop Hi.
  unfold SWMQueueAfterDrop, SWMQueuePendingState in *.
  unfold SWMQueueCoversAfterDrop, SWMQueueCoversWithPending in *.
  intuition eauto.
Qed.

Lemma SWMQueuePendingState_pop_back_dominated :
  forall (l q_l : list Z) (head tail i k : Z),
    head < tail ->
    Znth (Znth (tail - 1) q_l 0) l 0 <= Znth i l 0 ->
    SWMQueuePendingState l q_l head tail i k ->
    SWMQueuePendingState l q_l head (tail - 1) i k.
Proof.
  intros l q_l head tail i k Hnonempty Hdom Hstate.
  unfold SWMQueuePendingState in *.
  unfold SWMQueueEntriesValidAfterDrop, SWMQueueIndexIncreasing,
    SWMQueueValueDecreasing, SWMQueueCoversWithPending in *.
  destruct Hstate as
    [Hk1 [Hklen [Hi0 [Hilen [Hhead0 [Hhead_tail [Htail_len
      [Htail_i [Hvalid [Hinc [Hdec Hcover]]]]]]]]]]].
  repeat split; try lia; try (apply Hvalid; lia);
    try solve [intros; apply Hinc; lia | intros; apply Hdec; lia].
  intros idx Hidx0 Hidx_len Hidx_win.
  specialize (Hcover idx Hidx0 Hidx_len Hidx_win) as Hcov.
  destruct Hcov as [[pos [[Hpos_lo Hpos_hi] [Hidx_pos [Hpos_i Hval]]]] | Hval_i].
  - destruct (Z_lt_ge_dec pos (tail - 1)) as [Hpos_short | Hpos_last].
    + left. exists pos. repeat split; try lia; assumption.
    + right.
      assert (pos = tail - 1) by lia.
      subst pos.
      lia.
  - right; assumption.
Qed.

Lemma SWMQueuePendingState_push_current :
  forall (l q_l : list Z) (head tail i k : Z),
    Zlength q_l = Zlength l ->
    i < Zlength l ->
    SWMQueuePendingState l q_l head tail i k ->
    (head < tail ->
       Znth (Znth (tail - 1) q_l 0) l 0 > Znth i l 0) ->
    SWMQueueState l (replace_Znth tail i q_l) head (tail + 1) (i + 1) k.
Proof.
  intros l q_l head tail i k Hqlen Hi_lt Hstate Hlast_gt.
  unfold SWMQueuePendingState in Hstate.
  unfold SWMQueueState.
  unfold SWMQueueEntriesValidAfterDrop, SWMQueueEntriesValid,
    SWMQueueIndexIncreasing, SWMQueueValueDecreasing,
    SWMQueueCoversWithPending, SWMQueueCoversWindow in *.
  destruct Hstate as
    [Hk1 [Hklen [Hi0 [Hilen [Hhead0 [Hhead_tail [Htail_len
      [Htail_i [Hvalid [Hinc [Hdec Hcover]]]]]]]]]]].
  assert (Htail_nonneg : 0 <= tail) by lia.
  assert (Htail_bound : tail < Zlength q_l) by lia.
  assert (Htail_len_l : tail < Zlength l) by lia.
  assert (Hentries :
    forall pos : Z,
      head <= pos < tail + 1 ->
      0 <= Znth pos (replace_Znth tail i q_l) 0 /\
      Znth pos (replace_Znth tail i q_l) 0 < Zlength l /\
      i + 1 - k <= Znth pos (replace_Znth tail i q_l) 0 < i + 1).
  {
    intros pos Hpos.
    destruct (Z.eq_dec pos tail) as [-> | Hpos_ne].
    - rewrite Znth_replace_Znth_Same by lia.
      repeat split; lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      specialize (Hvalid pos ltac:(lia)) as [? [? ?]].
      repeat split; lia.
  }
  assert (Hindex :
    forall p q : Z,
      head <= p /\ p < q < tail + 1 ->
      Znth p (replace_Znth tail i q_l) 0 <
      Znth q (replace_Znth tail i q_l) 0).
  {
    intros p q Hpq.
    destruct (Z.eq_dec q tail) as [-> | Hq_ne].
    - rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      specialize (Hvalid p ltac:(lia)) as [? [? ?]].
      lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hinc; lia.
  }
  assert (Hvalue :
    forall p q : Z,
      head <= p /\ p < q < tail + 1 ->
      Znth (Znth p (replace_Znth tail i q_l) 0) l 0 >
      Znth (Znth q (replace_Znth tail i q_l) 0) l 0).
  {
    intros p q Hpq.
    destruct (Z.eq_dec q tail) as [-> | Hq_ne].
    - rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      assert (Hhead_lt_tail : head < tail) by lia.
      destruct (Z.eq_dec p (tail - 1)) as [-> | Hp_ne_last].
      + apply Hlast_gt; lia.
      + assert (p < tail - 1) by lia.
        specialize (Hdec p (tail - 1) ltac:(lia)) as Hdec_last.
        specialize (Hlast_gt Hhead_lt_tail) as Hlast.
        lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hdec; lia.
  }
  assert (Hcover_win :
    forall idx : Z,
      0 <= idx ->
      idx < Zlength l ->
      i + 1 - k <= idx < i + 1 ->
      exists pos : Z,
        head <= pos < tail + 1 /\
        idx <= Znth pos (replace_Znth tail i q_l) 0 /\
        Znth pos (replace_Znth tail i q_l) 0 < i + 1 /\
        Znth idx l 0 <= Znth (Znth pos (replace_Znth tail i q_l) 0) l 0).
  {
    intros idx Hidx0 Hidx_len Hidx_win.
    destruct (Z.eq_dec idx i) as [-> | Hidx_ne_i].
    - exists tail.
      rewrite Znth_replace_Znth_Same by lia.
      repeat split; try lia.
    - assert (Hidx_old_win : i - k < idx < i) by lia.
      specialize (Hcover idx Hidx0 Hidx_len Hidx_old_win) as Hcov.
      destruct Hcov as [[pos [[Hpos_lo Hpos_hi] [Hidx_pos [Hpos_i Hval]]]] | Hval_i].
      + exists pos.
        rewrite Znth_replace_Znth_Diff by lia.
        repeat split; try lia; assumption.
      + exists tail.
        rewrite Znth_replace_Znth_Same by lia.
        repeat split; try lia; assumption.
  }
  assert (Hhead_max :
    head < tail + 1 /\ k <= i + 1 ->
    WindowMaxValue l (i + 1 - k) (i + 1)
      (Znth (Znth head (replace_Znth tail i q_l) 0) l 0)).
  {
    intros [Hhead_nonempty Hk_proc].
    unfold WindowMaxValue, MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset, WindowUpperBoundValue.
    exists (Znth (Znth head (replace_Znth tail i q_l) 0) l 0).
    split.
    - split.
      + repeat split; try lia.
        destruct (Z.eq_dec head tail) as [Hhead_eq_tail | Hhead_ne_tail].
        * exists i.
          subst tail.
          rewrite Znth_replace_Znth_Same by lia.
          repeat split; try lia.
          intros idx Hidx_range.
          destruct (Z.eq_dec idx i) as [-> | Hidx_ne_i].
          -- lia.
          -- assert (Hidx_old_win : i - k < idx < i) by lia.
             specialize (Hcover idx ltac:(lia) ltac:(lia) Hidx_old_win) as Hcov.
             destruct Hcov as [[pos [[Hpos_lo Hpos_hi] [Hidx_pos [Hpos_i Hval]]]] | Hval_i].
             ++ lia.
             ++ assumption.
        * assert (head < tail) by lia.
          rewrite Znth_replace_Znth_Diff by lia.
          exists (Znth head q_l 0).
          specialize (Hvalid head ltac:(lia)) as [Hhead_idx0 [Hhead_idx_len Hhead_idx_win]].
          repeat split; try lia.
          intros idx Hidx_range.
          assert (Hhead_ge_current :
            Znth i l 0 <= Znth (Znth head q_l 0) l 0).
          {
            destruct (Z.eq_dec head (tail - 1)) as [-> | Hhead_ne_last].
            - specialize (Hlast_gt ltac:(lia)) as Hlast.
              lia.
            - assert (head < tail - 1) by lia.
              specialize (Hdec head (tail - 1) ltac:(lia)) as Hdec_last.
              specialize (Hlast_gt ltac:(lia)) as Hlast.
              lia.
          }
          destruct (Z.eq_dec idx i) as [-> | Hidx_ne_i].
          -- exact Hhead_ge_current.
          -- assert (Hidx_old_win : i - k < idx < i) by lia.
             specialize (Hcover idx ltac:(lia) ltac:(lia) Hidx_old_win) as Hcov.
             destruct Hcov as [[pos [[Hpos_lo Hpos_hi] [Hidx_pos [Hpos_i Hval]]]] | Hval_i].
             ++ assert (Hpos_head_cases : pos = head \/ head < pos) by lia.
                destruct Hpos_head_cases as [Hpos_eq_head | Hhead_lt_pos].
                ** subst pos; assumption.
                ** specialize (Hdec head pos ltac:(lia)) as Hdec_head.
                   lia.
             ++ lia.
      + intros ub Hub.
        unfold WindowUpperBoundValue in Hub.
        destruct Hub as [_ [_ [_ [pos [[Hpos_lo Hpos_hi] [Hub_eq Hub_upper]]]]]].
        subst ub.
        apply Hub_upper.
        destruct (Z.eq_dec head tail) as [Hhead_eq_tail | Hhead_ne_tail].
        * subst tail.
          rewrite Znth_replace_Znth_Same by lia.
          lia.
        * assert (head < tail) by lia.
          rewrite Znth_replace_Znth_Diff by lia.
          specialize (Hvalid head ltac:(lia)) as [_ [_ Hhead_win]].
          lia.
    - reflexivity.
  }
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [rewrite Zlength_replace_Znth; lia|].
  split; [lia|].
  split; [exact Hentries|].
  split; [exact Hindex|].
  split; [exact Hvalue|].
  split; [exact Hcover_win|].
  exact Hhead_max.
Qed.

Lemma SWMQueueState_window_max :
  forall (l q_l : list Z) (head tail processed k : Z),
    SWMQueueState l q_l head tail processed k ->
    head < tail ->
    k <= processed ->
    WindowMaxValue l (processed - k) processed (Znth (Znth head q_l 0) l 0).
Proof.
  intros l q_l head tail processed k Hstate Hhead Hprocessed.
  unfold SWMQueueState in Hstate.
  destruct Hstate as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax).
  apply Hmax; lia.
Qed.

Lemma SWMOutputPrefix_snoc :
  forall (l out : list Z) (k out_idx ans : Z),
    SWMOutputPrefix l k out_idx out ->
    out_idx < Zlength l - k + 1 ->
    WindowMaxValue l out_idx (out_idx + k) ans ->
    SWMOutputPrefix l k (out_idx + 1) (out ++ ans :: nil).
Proof.
  intros l out k out_idx ans Hprefix Hroom Hmax.
  unfold SWMOutputPrefix in *.
  destruct Hprefix as
    (Hk_pos & Hk_len & Hidx_nonneg & Hidx_bound & Hlen & Hprefix_values).
  repeat split; try lia.
  - rewrite Zlength_app_cons, Hlen; lia.
  - intros idx Hidx.
    destruct (Z_lt_ge_dec idx out_idx) as [Hlt | Hge].
    + rewrite app_Znth1 by (rewrite Hlen; lia).
      apply Hprefix_values; lia.
    + assert (idx = out_idx) by lia; subst idx.
      rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite Hlen.
      replace (out_idx - out_idx) with 0 by lia.
      rewrite Znth0_cons.
      exact Hmax.
Qed.

Lemma SWMOutputPrefix_complete :
  forall (l out : list Z) (k out_idx : Z),
    SWMOutputPrefix l k out_idx out ->
    out_idx = Zlength l - k + 1 ->
    SlidingWindowMaximum l k out.
Proof.
  intros l out k out_idx Hprefix Hcomplete.
  unfold SWMOutputPrefix in Hprefix.
  unfold SlidingWindowMaximum.
  destruct Hprefix as
    (Hk_pos & Hk_len & Hidx_nonneg & Hidx_bound & Hlen & Hprefix_values).
  split; [lia |].
  split; [lia |].
  split.
  - rewrite Hlen, Hcomplete; reflexivity.
  - intros idx Hidx.
    apply Hprefix_values.
    rewrite <- Hlen; exact Hidx.
Qed.
