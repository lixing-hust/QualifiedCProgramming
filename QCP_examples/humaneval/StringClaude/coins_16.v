Load "../spec/16".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

Definition is_upper_zb (c : Z) : bool :=
  Z.leb 65 c && Z.leb c 90.

Definition lower_z (c : Z) : Z :=
  if is_upper_zb c then c + 32 else c.

Definition problem_16_pre_z (s : list Z) : Prop :=
  problem_16_pre (string_of_list_z s).

Definition problem_16_spec_z (s : list Z) (output : Z) : Prop :=
  0 <= output /\
  problem_16_spec (string_of_list_z s) (Z.to_nat output).

Fixpoint mem_zb (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | y :: ys => if Z.eqb x y then true else mem_zb x ys
  end.

Definition add_unique_z (x : Z) (seen : list Z) : list Z :=
  if mem_zb x seen then seen else x :: seen.

Fixpoint collect_lower_z (seen input : list Z) : list Z :=
  match input with
  | [] => seen
  | x :: xs => collect_lower_z (add_unique_z (lower_z x) seen) xs
  end.

Definition distinct_lower_prefix_z (i : Z) (input : list Z) : list Z :=
  collect_lower_z [] (sublist 0 i input).

Definition count_distinct_lower_upto (i : Z) (input : list Z) : Z :=
  Z.of_nat (List.length (distinct_lower_prefix_z i input)).

Definition lower_seen_state_z
  (j i : Z) (input : list Z) (c seen : Z) : Prop :=
  (seen = 0 \/ seen = 1) /\
  c = lower_z (Znth i input 0) /\
  (seen = 1 ->
    exists k, 0 <= k < j /\ lower_z (Znth k input 0) = c) /\
  (seen = 0 ->
    forall k, 0 <= k < j -> lower_z (Znth k input 0) <> c).

Lemma mem_zb_true_iff : forall x l,
  mem_zb x l = true <-> In x l.
Proof.
  intros x l.
  induction l as [| y ys IH]; simpl.
  - split; intros H; [discriminate | contradiction].
  - destruct (Z.eqb_spec x y) as [-> | Hne].
    + split; intros _; [left; reflexivity | reflexivity].
    + rewrite IH.
      split.
      * intros H. right; exact H.
      * intros [H | H]; [congruence | exact H].
Qed.

Lemma mem_zb_false_iff : forall x l,
  mem_zb x l = false <-> ~ In x l.
Proof.
  intros x l.
  destruct (mem_zb x l) eqn:Hmem.
  - rewrite mem_zb_true_iff in Hmem.
    split; [discriminate | intros Hnot; contradiction].
  - split; [| reflexivity].
    intros _ Hin.
    rewrite <- mem_zb_true_iff in Hin.
    congruence.
Qed.

Lemma add_unique_in_iff : forall x y seen,
  In y (add_unique_z x seen) <-> y = x \/ In y seen.
Proof.
  intros x y seen.
  unfold add_unique_z.
  destruct (mem_zb x seen) eqn:Hmem.
  - rewrite mem_zb_true_iff in Hmem.
    split.
    + intros Hin. right; exact Hin.
    + intros [-> | Hin]; assumption.
  - split.
    + intros [-> | Hin]; [left; reflexivity | right; exact Hin].
    + intros [-> | Hin]; [left; reflexivity | right; exact Hin].
Qed.

Lemma add_unique_NoDup : forall x seen,
  NoDup seen ->
  NoDup (add_unique_z x seen).
Proof.
  intros x seen Hnd.
  unfold add_unique_z.
  destruct (mem_zb x seen) eqn:Hmem; [exact Hnd |].
  constructor; [rewrite mem_zb_false_iff in Hmem; exact Hmem | exact Hnd].
Qed.

Lemma collect_lower_NoDup : forall input seen,
  NoDup seen ->
  NoDup (collect_lower_z seen input).
Proof.
  induction input as [| x xs IH]; intros seen Hnd; simpl.
  - exact Hnd.
  - apply IH. apply add_unique_NoDup. exact Hnd.
Qed.

Lemma collect_lower_in_iff : forall input seen y,
  In y (collect_lower_z seen input) <->
  In y seen \/ exists x, In x input /\ y = lower_z x.
Proof.
  induction input as [| x xs IH]; intros seen y; simpl.
  - split; intros H.
    + left; exact H.
    + destruct H as [H | [x [H _]]]; [exact H | contradiction].
  - rewrite IH.
    rewrite add_unique_in_iff.
    split.
    + intros [[Hy | Hy] | [z [Hz Hzy]]].
      * right. exists x. split; [left; reflexivity | exact Hy].
      * left. exact Hy.
      * right. exists z. split; [right; exact Hz | exact Hzy].
    + intros [Hy | [z [[-> | Hz] Hzy]]].
      * left. right. exact Hy.
      * left. left. exact Hzy.
      * right. exists z. split; [exact Hz | exact Hzy].
Qed.

Lemma collect_lower_app : forall l2 l1 seen,
  collect_lower_z seen (l1 ++ l2) =
  collect_lower_z (collect_lower_z seen l1) l2.
Proof.
  induction l1 as [| x xs IH]; intros seen; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma collect_lower_length_le : forall input seen,
  (List.length (collect_lower_z seen input) <=
   List.length seen + List.length input)%nat.
Proof.
  induction input as [| x xs IH]; intros seen; simpl.
  - lia.
  - unfold add_unique_z.
    destruct (mem_zb (lower_z x) seen) eqn:Hmem.
    + specialize (IH seen). lia.
    + specialize (IH (lower_z x :: seen)). simpl in IH. lia.
Qed.

Lemma lower_z_range : forall c,
  0 <= c < 256 ->
  0 <= lower_z c < 256.
Proof.
  intros c Hc.
  unfold lower_z, is_upper_zb.
  destruct (Z.leb 65 c && Z.leb c 90) eqn:H; lia.
Qed.

Lemma lower_z_upper : forall c,
  65 <= c <= 90 ->
  lower_z c = c + 32.
Proof.
  intros c Hc.
  unfold lower_z, is_upper_zb.
  rewrite (proj2 (Z.leb_le 65 c)) by lia.
  rewrite (proj2 (Z.leb_le c 90)) by lia.
  reflexivity.
Qed.

Lemma lower_z_low : forall c,
  c < 65 ->
  lower_z c = c.
Proof.
  intros c Hc.
  unfold lower_z, is_upper_zb.
  rewrite (proj2 (Z.leb_gt 65 c)) by lia.
  reflexivity.
Qed.

Lemma lower_z_high : forall c,
  c > 90 ->
  lower_z c = c.
Proof.
  intros c Hc.
  unfold lower_z, is_upper_zb.
  rewrite (proj2 (Z.leb_gt c 90)) by lia.
  destruct (Z.leb 65 c); reflexivity.
Qed.

Lemma count_distinct_lower_upto_zero : forall input,
  count_distinct_lower_upto 0 input = 0.
Proof.
  intros input.
  unfold count_distinct_lower_upto, distinct_lower_prefix_z.
  unfold sublist.
  simpl.
  reflexivity.
Qed.

Lemma count_distinct_lower_upto_nonneg : forall i input,
  0 <= count_distinct_lower_upto i input.
Proof.
  intros i input.
  unfold count_distinct_lower_upto.
  lia.
Qed.


Lemma ascii_of_z_inj_16 : forall x y,
  0 <= x < 256 ->
  0 <= y < 256 ->
  ascii_of_z x = ascii_of_z y ->
  x = y.
Proof.
  intros x y Hx Hy H.
  apply f_equal with (f := nat_of_ascii) in H.
  rewrite !nat_of_ascii_ascii_of_z in H by assumption.
  lia.
Qed.

Lemma lower_ascii_of_z : forall c,
  0 <= c < 256 ->
  lower (ascii_of_z c) = ascii_of_z (lower_z c).
Proof.
  intros c Hc.
  unfold lower, is_upper, lower_z, is_upper_zb.
  rewrite nat_of_ascii_ascii_of_z by exact Hc.
  destruct (Z.leb 65 c && Z.leb c 90) eqn:Hupper.
  - apply andb_true_iff in Hupper as [Hlo Hhi].
    apply Z.leb_le in Hlo.
    apply Z.leb_le in Hhi.
    assert (((65 <=? Z.to_nat c) && (Z.to_nat c <=? 90))%nat = true).
    {
      apply andb_true_iff.
      split; apply Nat.leb_le; lia.
    }
    rewrite H.
    unfold ascii_of_z.
    replace (Z.to_nat (c + 32)) with (Z.to_nat c + 32)%nat by lia.
    reflexivity.
  - assert (((65 <=? Z.to_nat c) && (Z.to_nat c <=? 90))%nat = false).
    {
      apply andb_false_iff in Hupper.
      apply andb_false_iff.
      destruct Hupper as [Hupper | Hupper].
      - left. apply Z.leb_gt in Hupper. apply Nat.leb_gt. lia.
      - right. apply Z.leb_gt in Hupper. apply Nat.leb_gt. lia.
    }
    rewrite H.
    reflexivity.
Qed.

Lemma lower_seen_state_init : forall i input c,
  c = lower_z (Znth i input 0) ->
  lower_seen_state_z 0 i input c 0.
Proof.
  unfold lower_seen_state_z.
  intros i input c Hc.
  repeat split; auto; try lia.
Qed.

Lemma lower_seen_state_step_hit : forall j i input c seen,
  0 <= j ->
  lower_seen_state_z j i input c seen ->
  lower_z (Znth j input 0) = c ->
  lower_seen_state_z (j + 1) i input c 1.
Proof.
  unfold lower_seen_state_z.
  intros j i input c seen Hj [_ [Hc _]] Hhit.
  repeat split.
  - right; reflexivity.
  - exact Hc.
  - intros _. exists j. split; [lia | exact Hhit].
  - intros Hbad. discriminate Hbad.
Qed.

Lemma lower_seen_state_step_miss : forall j i input c seen,
  0 <= j ->
  lower_seen_state_z j i input c seen ->
  lower_z (Znth j input 0) <> c ->
  lower_seen_state_z (j + 1) i input c seen.
Proof.
  unfold lower_seen_state_z.
  intros j i input c seen Hj [Hseen [Hc [Hone Hzero]]] Hmiss.
  repeat split; auto.
  - intros H1.
    destruct (Hone H1) as [k [Hk Hkval]].
    exists k. split; [lia | exact Hkval].
  - intros H0 k Hk.
    destruct (Z.eq_dec k j) as [-> | Hne]; [exact Hmiss |].
    apply Hzero; [exact H0 | lia].
Qed.

Lemma distinct_lower_prefix_step_seen : forall i input,
  0 <= i < Zlength input ->
  (exists k, 0 <= k < i /\ lower_z (Znth k input 0) = lower_z (Znth i input 0)) ->
  count_distinct_lower_upto (i + 1) input =
  count_distinct_lower_upto i input.
Proof.
  intros i input Hi [k [Hk Hsame]].
  unfold count_distinct_lower_upto, distinct_lower_prefix_z.
  rewrite (@sublist_split Z 0 (i + 1) i input).
  2:{ split; lia. }
  2:{ rewrite <- Zlength_correct. lia. }
  rewrite (@sublist_single Z i input 0) by (rewrite <- Zlength_correct; lia).
  rewrite collect_lower_app.
  cbn [collect_lower_z].
  unfold add_unique_z.
  destruct (mem_zb (lower_z (Znth i input 0)) (collect_lower_z [] (sublist 0 i input))) eqn:Hmem.
  - reflexivity.
  - rewrite mem_zb_false_iff in Hmem.
    exfalso. apply Hmem.
    rewrite collect_lower_in_iff.
    right. exists (Znth k input 0).
    split.
    + replace (Znth k input 0) with (Znth k (sublist 0 i input) 0).
      2:{
        pose proof (@Znth_sublist Z 0 k i input 0 ltac:(lia) ltac:(lia)) as Hz.
        replace (k + 0) with k in Hz by lia.
        exact Hz.
      }
      unfold Znth.
      apply nth_In.
      apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct.
      rewrite Zlength_sublist by lia.
      lia.
    + symmetry. exact Hsame.
Qed.

Lemma distinct_lower_prefix_step_new : forall i input,
  0 <= i < Zlength input ->
  (forall k, 0 <= k < i -> lower_z (Znth k input 0) <> lower_z (Znth i input 0)) ->
  count_distinct_lower_upto (i + 1) input =
  count_distinct_lower_upto i input + 1.
Proof.
  intros i input Hi Hnew.
  unfold count_distinct_lower_upto, distinct_lower_prefix_z.
  rewrite (@sublist_split Z 0 (i + 1) i input).
  2:{ split; lia. }
  2:{ rewrite <- Zlength_correct. lia. }
  rewrite (@sublist_single Z i input 0) by (rewrite <- Zlength_correct; lia).
  rewrite collect_lower_app.
  cbn [collect_lower_z].
  unfold add_unique_z.
  destruct (mem_zb (lower_z (Znth i input 0)) (collect_lower_z [] (sublist 0 i input))) eqn:Hmem.
  - rewrite mem_zb_true_iff in Hmem.
    rewrite collect_lower_in_iff in Hmem.
    destruct Hmem as [Hbad | [x [Hin Hx]]]; [contradiction |].
    apply In_nth with (d := 0) in Hin.
    destruct Hin as [kn [Hkn Hnth]].
    exfalso.
    apply (Hnew (Z.of_nat kn)).
    + apply Nat2Z.inj_lt in Hkn.
      rewrite <- Zlength_correct in Hkn.
      rewrite Zlength_sublist in Hkn by lia.
      lia.
    + replace x with (Znth (Z.of_nat kn) (sublist 0 i input) 0) in Hx.
      2:{
        unfold Znth.
        rewrite Nat2Z.id.
        exact Hnth.
      }
      assert (HknZ : 0 <= Z.of_nat kn < i).
      {
        apply Nat2Z.inj_lt in Hkn.
        rewrite <- Zlength_correct in Hkn.
        rewrite Zlength_sublist in Hkn by lia.
        lia.
      }
      rewrite (@Znth_sublist Z 0 (Z.of_nat kn) i input 0) in Hx by lia.
      replace (Z.of_nat kn + 0) with (Z.of_nat kn) in Hx by lia.
      symmetry. exact Hx.
  - simpl. lia.
Qed.

Lemma distinct_lower_prefix_NoDup : forall i input,
  NoDup (distinct_lower_prefix_z i input).
Proof.
  intros i input.
  unfold distinct_lower_prefix_z.
  apply collect_lower_NoDup.
  constructor.
Qed.

Lemma distinct_lower_prefix_range : forall i input x,
  0 <= i <= Zlength input ->
  ascii_range_z input ->
  In x (distinct_lower_prefix_z i input) ->
  0 <= x < 256.
Proof.
  intros i input x Hi Hrange Hin.
  unfold distinct_lower_prefix_z in Hin.
  rewrite collect_lower_in_iff in Hin.
  destruct Hin as [Hin | [y [Hy ->]]]; [contradiction |].
  apply In_nth with (d := 0) in Hy.
  destruct Hy as [kn [Hkn Hnth]].
  apply lower_z_range.
  rewrite <- Hnth.
  replace (nth kn (sublist 0 i input) 0)
    with (Znth (Z.of_nat kn) (sublist 0 i input) 0).
  2:{ unfold Znth; rewrite Nat2Z.id; reflexivity. }
  assert (HknZ : 0 <= Z.of_nat kn < i).
  {
    apply Nat2Z.inj_lt in Hkn.
    rewrite <- Zlength_correct in Hkn.
    rewrite Zlength_sublist in Hkn by lia.
    lia.
  }
  rewrite (@Znth_sublist Z 0 (Z.of_nat kn) i input 0) by lia.
  apply Hrange.
  lia.
Qed.

Lemma NoDup_map_ascii_of_z_16 : forall l,
  (forall x, In x l -> 0 <= x < 256) ->
  NoDup l ->
  NoDup (map ascii_of_z l).
Proof.
  intros l Hrange Hnd.
  induction Hnd as [| x xs Hnotin Hnd IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hy Hiny]].
      apply ascii_of_z_inj_16 in Hy; try (apply Hrange; simpl; auto).
      subst y. contradiction.
    + apply IH. intros y Hy. apply Hrange. simpl; auto.
Qed.

Lemma sublist_full_16 : forall (input : list Z),
  sublist 0 (Zlength input) input = input.
Proof.
  intros input.
  unfold sublist.
  rewrite skipn_O.
  rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (List.length input))) with
    (List.length input) by lia.
  apply firstn_all.
Qed.

Lemma Znth_In_16 : forall input k,
  0 <= k < Zlength input ->
  In (Znth k input 0) input.
Proof.
  intros input k Hk.
  unfold Znth.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma problem_16_spec_z_count : forall input,
  ascii_range_z input ->
  problem_16_spec_z input (count_distinct_lower_upto (Zlength input) input).
Proof.
  intros input Hrange.
  unfold problem_16_spec_z.
  split.
  - unfold count_distinct_lower_upto. lia.
  - unfold problem_16_spec.
    set (dl := distinct_lower_prefix_z (Zlength input) input).
    exists (map ascii_of_z dl).
    split.
    + apply NoDup_map_ascii_of_z_16.
      * intros x Hx.
        unfold dl in Hx.
        eapply distinct_lower_prefix_range.
        -- split.
           ++ apply (@Zlength_nonneg Z input).
           ++ apply Z.le_refl.
        -- exact Hrange.
        -- exact Hx.
      * unfold dl. apply distinct_lower_prefix_NoDup.
    + split.
      * intros idx Hidx.
        rewrite string_get_string_of_list_z by
          (rewrite string_of_list_z_length in Hidx; lia).
        rewrite lower_ascii_of_z.
        -- apply in_map.
           unfold dl, distinct_lower_prefix_z.
           rewrite collect_lower_in_iff.
           right.
           exists (nth idx input 0).
           split.
           ++ rewrite sublist_full_16.
              apply nth_In.
              rewrite <- string_of_list_z_length.
              exact Hidx.
           ++ reflexivity.
        -- pose proof (Hrange (Z.of_nat idx)) as Hr.
           assert (0 <= Z.of_nat idx < Zlength input).
           {
             rewrite string_of_list_z_length in Hidx.
             rewrite Zlength_correct.
             lia.
           }
           specialize (Hr H).
           unfold Znth in Hr.
           rewrite Nat2Z.id in Hr.
           exact Hr.
      * split.
        -- intros d Hd.
           apply in_map_iff in Hd.
           destruct Hd as [z [Hzd HzIn]].
           unfold dl, distinct_lower_prefix_z in HzIn.
           rewrite collect_lower_in_iff in HzIn.
           destruct HzIn as [HzIn | [y [Hy Hz]]]; [contradiction |].
           subst z.
           rewrite sublist_full_16 in Hy.
           apply In_nth with (d := 0) in Hy.
           destruct Hy as [idx [Hidx Hnth]].
           exists idx.
           split.
           ++ rewrite string_of_list_z_length. lia.
           ++ rewrite string_get_string_of_list_z by lia.
              rewrite Hnth.
              rewrite lower_ascii_of_z.
              ** symmetry. exact Hzd.
              ** assert (Hy_range : 0 <= y < 256).
                 {
                   pose proof (Hrange (Z.of_nat idx)) as Hr.
                   assert (0 <= Z.of_nat idx < Zlength input).
                   { rewrite Zlength_correct. lia. }
                   specialize (Hr H).
                   unfold Znth in Hr.
                   rewrite Nat2Z.id in Hr.
                   rewrite Hnth in Hr.
                   exact Hr.
                 }
                 exact Hy_range.
        -- unfold count_distinct_lower_upto, dl.
           rewrite map_length.
           rewrite Nat2Z.id.
           reflexivity.
Qed.
