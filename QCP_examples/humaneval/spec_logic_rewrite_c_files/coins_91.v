Load "../spec/91".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.
Load "../StringClaude/string_bridge".
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_91_pre_z (input : list Z) : Prop :=
  problem_91_pre (string_of_list_z input).

Definition problem_91_spec_z (input : list Z) (output : Z) : Prop :=
  problem_91_spec (string_of_list_z input) (Z.to_nat output).

Definition zbool_91 (b : bool) : Z := if b then 1 else 0.

Definition bored_is_space_z (c : Z) : bool := Z.eqb c 32.
Definition bored_is_i_z (c : Z) : bool := Z.eqb c 73.
Definition bored_is_delimiter_z (c : Z) : bool :=
  orb (orb (Z.eqb c 46) (Z.eqb c 63)) (Z.eqb c 33).

Definition bored_add_z (c isi : Z) : Z :=
  zbool_91 (andb (bored_is_space_z c) (Z.eqb isi 1)).

Definition bored_next_isi_z (c isstart : Z) : Z :=
  zbool_91 (andb (bored_is_i_z c) (Z.eqb isstart 1)).

Definition bored_next_isstart_z (c isstart : Z) : Z :=
  if bored_is_delimiter_z c then 1
  else if bored_is_space_z c then isstart
  else 0.

Fixpoint bored_state_after_nat_91
    (k : nat) (input : list Z) : Z * Z * Z :=
  match k with
  | O => (0, 1, 0)
  | S k' =>
      let '(sum, isstart, isi) := bored_state_after_nat_91 k' input in
      let c := Znth (Z.of_nat k') input 0 in
      (sum + bored_add_z c isi,
       bored_next_isstart_z c isstart,
       bored_next_isi_z c isstart)
  end.

Definition bored_sum_prefix_z (i : Z) (input : list Z) : Z :=
  let '(sum, _, _) := bored_state_after_nat_91 (Z.to_nat i) input in sum.

Definition bored_isstart_prefix_z (i : Z) (input : list Z) : Z :=
  let '(_, isstart, _) := bored_state_after_nat_91 (Z.to_nat i) input in
  isstart.

Definition bored_isi_prefix_z (i : Z) (input : list Z) : Z :=
  let '(_, _, isi) := bored_state_after_nat_91 (Z.to_nat i) input in isi.

Lemma bored_state_after_step_91 : forall i input sum isstart isi,
  0 <= i ->
  bored_state_after_nat_91 (Z.to_nat i) input = (sum, isstart, isi) ->
  bored_state_after_nat_91 (Z.to_nat (i + 1)) input =
    (sum + bored_add_z (Znth i input 0) isi,
     bored_next_isstart_z (Znth i input 0) isstart,
     bored_next_isi_z (Znth i input 0) isstart).
Proof.
  intros i input sum isstart isi Hi Hstate.
  rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1%nat.
  rewrite Nat.add_1_r.
  simpl.
  rewrite Z2Nat.id by lia.
  rewrite Hstate.
  reflexivity.
Qed.

Lemma bored_sum_prefix_step_91 : forall i input,
  0 <= i ->
  bored_sum_prefix_z (i + 1) input =
  bored_sum_prefix_z i input +
  bored_add_z (Znth i input 0) (bored_isi_prefix_z i input).
Proof.
  intros i input Hi.
  unfold bored_sum_prefix_z, bored_isi_prefix_z.
  destruct (bored_state_after_nat_91 (Z.to_nat i) input)
    as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step_91 i input sum isstart isi Hi Hstate).
  reflexivity.
Qed.

Lemma bored_isstart_prefix_step_91 : forall i input,
  0 <= i ->
  bored_isstart_prefix_z (i + 1) input =
  bored_next_isstart_z (Znth i input 0)
    (bored_isstart_prefix_z i input).
Proof.
  intros i input Hi.
  unfold bored_isstart_prefix_z.
  destruct (bored_state_after_nat_91 (Z.to_nat i) input)
    as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step_91 i input sum isstart isi Hi Hstate).
  reflexivity.
Qed.

Lemma bored_isi_prefix_step_91 : forall i input,
  0 <= i ->
  bored_isi_prefix_z (i + 1) input =
  bored_next_isi_z (Znth i input 0)
    (bored_isstart_prefix_z i input).
Proof.
  intros i input Hi.
  unfold bored_isi_prefix_z, bored_isstart_prefix_z.
  destruct (bored_state_after_nat_91 (Z.to_nat i) input)
    as [[sum isstart] isi] eqn:Hstate.
  rewrite (bored_state_after_step_91 i input sum isstart isi Hi Hstate).
  reflexivity.
Qed.

Lemma bored_add_z_range_91 : forall c isi,
  0 <= bored_add_z c isi <= 1.
Proof.
  intros c isi.
  unfold bored_add_z, zbool_91.
  destruct (bored_is_space_z c && (isi =? 1)); lia.
Qed.

Lemma bored_next_isi_z_range_91 : forall c isstart,
  bored_next_isi_z c isstart = 0 \/
  bored_next_isi_z c isstart = 1.
Proof.
  intros c isstart.
  unfold bored_next_isi_z, zbool_91.
  destruct (bored_is_i_z c && (isstart =? 1)); lia.
Qed.

Lemma bored_next_isstart_z_range_91 : forall c isstart,
  (isstart = 0 \/ isstart = 1) ->
  bored_next_isstart_z c isstart = 0 \/
  bored_next_isstart_z c isstart = 1.
Proof.
  intros c isstart Hrange.
  unfold bored_next_isstart_z.
  destruct (bored_is_delimiter_z c); auto.
  destruct (bored_is_space_z c); auto.
Qed.

Lemma bored_state_after_nat_range_91 : forall n input sum isstart isi,
  bored_state_after_nat_91 n input = (sum, isstart, isi) ->
  0 <= sum <= Z.of_nat n /\
  (isstart = 0 \/ isstart = 1) /\
  (isi = 0 \/ isi = 1).
Proof.
  induction n as [| n IH]; intros input sum isstart isi Hstate.
  - simpl in Hstate.
    inversion Hstate; subst.
    repeat split; lia.
  - simpl in Hstate.
    destruct (bored_state_after_nat_91 n input)
      as [[sum0 isstart0] isi0] eqn:Hprev.
    inversion Hstate; subst; clear Hstate.
    specialize (IH input sum0 isstart0 isi0 Hprev).
    destruct IH as [Hsum [Hisstart Hisi]].
    pose proof (bored_add_z_range_91
      (Znth (Z.of_nat n) input 0) isi0) as Hadd.
    split; [lia |].
    split.
    + apply bored_next_isstart_z_range_91; exact Hisstart.
    + apply bored_next_isi_z_range_91.
Qed.

Lemma bored_state_range_91 : forall i input,
  0 <= i ->
  0 <= bored_sum_prefix_z i input <= i /\
  (bored_isstart_prefix_z i input = 0 \/
   bored_isstart_prefix_z i input = 1) /\
  (bored_isi_prefix_z i input = 0 \/
   bored_isi_prefix_z i input = 1).
Proof.
  intros i input Hi.
  unfold bored_sum_prefix_z, bored_isstart_prefix_z,
    bored_isi_prefix_z.
  destruct (bored_state_after_nat_91 (Z.to_nat i) input)
    as [[sum isstart] isi] eqn:Hstate.
  pose proof (bored_state_after_nat_range_91
    (Z.to_nat i) input sum isstart isi Hstate) as Hrange.
  rewrite Z2Nat.id in Hrange by lia.
  exact Hrange.
Qed.


Definition bored_followb_91 (j : nat) (input : list Z) : bool :=
  match j with
  | O => false
  | S i =>
      (Znth (Z.of_nat j) input 0 =? 32) &&
      ((Znth (Z.of_nat i) input 0 =? 73) &&
       (bored_isstart_prefix_z (Z.of_nat i) input =? 1))
  end.

Lemma bored_isi_prefix_nat_91 : forall i input,
  bored_isi_prefix_z (Z.of_nat (S i)) input =
  bored_next_isi_z (Znth (Z.of_nat i) input 0)
    (bored_isstart_prefix_z (Z.of_nat i) input).
Proof.
  intros i input.
  replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia.
  apply bored_isi_prefix_step_91; lia.
Qed.

Lemma bored_add_at_followb_91 : forall j input,
  bored_add_z (Znth (Z.of_nat j) input 0)
    (bored_isi_prefix_z (Z.of_nat j) input) =
  zbool_91 (bored_followb_91 j input).
Proof.
  intros [| i] input.
  - change (bored_add_z (Znth 0 input 0) 0 = 0).
    unfold bored_add_z, zbool_91. rewrite andb_false_r. reflexivity.
  - rewrite bored_isi_prefix_nat_91.
    unfold bored_add_z, bored_next_isi_z, bored_followb_91,
      bored_is_space_z, bored_is_i_z, zbool_91.
    destruct (Znth (Z.of_nat (S i)) input 0 =? 32),
      (Znth (Z.of_nat i) input 0 =? 73),
      (bored_isstart_prefix_z (Z.of_nat i) input =? 1);
      reflexivity.
Qed.

Lemma bored_sum_filter_91 : forall n input,
  bored_sum_prefix_z (Z.of_nat n) input =
  Z.of_nat (List.length (filter (fun j => bored_followb_91 j input)
    (seq 0 n))).
Proof.
  induction n as [| n IH]; intros input.
  - reflexivity.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite bored_sum_prefix_step_91 by lia.
    rewrite IH, bored_add_at_followb_91.
    rewrite seq_S, filter_app, length_app; simpl.
    unfold zbool_91.
    destruct (bored_followb_91 n input); simpl;
      rewrite Nat2Z.inj_add; simpl; lia.
Qed.

Definition z_sentence_delimiter_91 (c : Z) : Prop :=
  c = 46 \/ c = 63 \/ c = 33.

Definition z_sentence_start_91
    (input : list Z) (start : nat) : Prop :=
  start = O \/
  exists delimiter_pos delimiter,
    start = S delimiter_pos /\
    nth_error input delimiter_pos = Some delimiter /\
    z_sentence_delimiter_91 delimiter.

Definition z_begins_sentence_at_91
    (input : list Z) (i : nat) : Prop :=
  exists start,
    z_sentence_start_91 input start /\
    (start <= i)%nat /\
    forall j, (start <= j < i)%nat -> nth_error input j = Some 32.

Definition z_boredom_at_91 (input : list Z) (i : nat) : Prop :=
  z_begins_sentence_at_91 input i /\
  nth_error input i = Some 73 /\
  nth_error input (S i) = Some 32.

Lemma nth_error_Znth_nat_91 : forall (input : list Z) i,
  (i < List.length input)%nat ->
  nth_error input i = Some (Znth (Z.of_nat i) input 0).
Proof.
  intros input i Hi.
  unfold Znth.
  rewrite Nat2Z.id.
  apply (@nth_error_nth' Z); exact Hi.
Qed.

Lemma z_begins_zero_91 : forall input,
  z_begins_sentence_at_91 input O.
Proof.
  intros input. exists O. repeat split.
  - left; reflexivity.
  - lia.
  - intros; lia.
Qed.

Lemma z_begins_succ_91 : forall input i,
  (S i <= List.length input)%nat ->
  (z_begins_sentence_at_91 input (S i) <->
   (exists c, nth_error input i = Some c /\ z_sentence_delimiter_91 c) \/
   (z_begins_sentence_at_91 input i /\ nth_error input i = Some 32)).
Proof.
  intros input i Hibound. split.
  - intros (start & Hstart & Hle & Hspaces).
    destruct (Nat.eq_dec start (S i)) as [Heq | Hneq].
    + subst start. left.
      destruct Hstart as [Hzero | (d & c & Hstart & Hnth & Hdelim)].
      * lia.
      * inversion Hstart; subst d. eauto.
    + right. split.
      * exists start. repeat split; try assumption.
        -- lia.
        -- intros j Hj. apply Hspaces. lia.
      * apply Hspaces. lia.
  - intros [(c & Hnth & Hdelim) | (Hbegin & Hspace)].
    + exists (S i). repeat split.
      * right. exists i, c. repeat split; assumption.
      * lia.
      * intros; lia.
    + destruct Hbegin as (start & Hstart & Hle & Hspaces).
      exists start. repeat split; try assumption.
      * lia.
      * intros j Hj.
        destruct (Nat.eq_dec j i) as [-> | Hneq]; auto.
        apply Hspaces. lia.
Qed.

Lemma bored_isstart_begins_91 : forall input i,
  (i <= List.length input)%nat ->
  (bored_isstart_prefix_z (Z.of_nat i) input = 1 <->
   z_begins_sentence_at_91 input i).
Proof.
  induction i as [| i IH]; intros Hbound.
  - split; intros.
    + apply z_begins_zero_91.
    + reflexivity.
  - replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia.
    rewrite bored_isstart_prefix_step_91 by lia.
    rewrite z_begins_succ_91 by exact Hbound.
    assert (Hi : (i < List.length input)%nat) by lia.
    rewrite (nth_error_Znth_nat_91 input i Hi).
    pose proof (bored_state_range_91 (Z.of_nat i) input ltac:(lia))
      as (_ & Hstart_range & _).
    specialize (IH ltac:(lia)).
    unfold bored_next_isstart_z, bored_is_delimiter_z,
      bored_is_space_z, z_sentence_delimiter_91.
    destruct Hstart_range as [Hstart | Hstart];
      rewrite Hstart in *;
      destruct (Znth (Z.of_nat i) input 0 =? 46) eqn:E46;
      destruct (Znth (Z.of_nat i) input 0 =? 63) eqn:E63;
      destruct (Znth (Z.of_nat i) input 0 =? 33) eqn:E33;
      destruct (Znth (Z.of_nat i) input 0 =? 32) eqn:E32;
      simpl in *;
      apply Z.eqb_eq in E46 || apply Z.eqb_neq in E46;
      apply Z.eqb_eq in E63 || apply Z.eqb_neq in E63;
      apply Z.eqb_eq in E33 || apply Z.eqb_neq in E33;
      apply Z.eqb_eq in E32 || apply Z.eqb_neq in E32;
      firstorder congruence.
Qed.
Lemma bored_followb_z_boredom_91 : forall input i,
  (S i < List.length input)%nat ->
  (bored_followb_91 (S i) input = true <->
   z_boredom_at_91 input i).
Proof.
  intros input i Hbound.
  unfold bored_followb_91, z_boredom_at_91.
  rewrite !andb_true_iff, !Z.eqb_eq.
  rewrite (bored_isstart_begins_91 input i) by lia.
  rewrite (nth_error_Znth_nat_91 input i) by lia.
  rewrite (nth_error_Znth_nat_91 input (S i)) by lia.
  firstorder congruence.
Qed.

Lemma nth_error_map_ascii_of_z_91 : forall input i a,
  nth_error (map ascii_of_z input) i = Some a <->
  exists c, nth_error input i = Some c /\ ascii_of_z c = a.
Proof.
  induction input as [| c input IH]; intros [| i] a; simpl.
  - split; [discriminate | intros (? & H & _); discriminate].
  - split; [discriminate | intros (? & H & _); discriminate].
  - split.
    + intros H. inversion H; subst. eauto.
    + intros (c' & Hc & Ha). inversion Hc; subst. congruence.
  - apply IH.
Qed.

Lemma all_ascii_nth_error_91 : forall input i c,
  all_ascii input ->
  nth_error input i = Some c ->
  0 <= c <= 127.
Proof.
  intros input i c Hall Hnth.
  assert (Hi : (i < List.length input)%nat).
  { apply nth_error_Some. congruence. }
  specialize (Hall (Z.of_nat i)).
  rewrite Zlength_correct in Hall.
  assert (0 <= Z.of_nat i < Z.of_nat (List.length input)) by lia.
  specialize (Hall H).
  pose proof (nth_error_Znth_nat_91 input i Hi) as Hznth.
  rewrite Hnth in Hznth. inversion Hznth; subst. exact Hall.
Qed.

Lemma ascii_of_z_7bit_inj_91 : forall c d,
  0 <= c <= 127 ->
  0 <= d <= 127 ->
  ascii_of_z c = ascii_of_z d ->
  c = d.
Proof.
  intros c d Hc Hd Heq.
  apply (f_equal nat_of_ascii) in Heq.
  rewrite !nat_of_ascii_ascii_of_z in Heq by lia.
  lia.
Qed.

Lemma ascii_of_z_space_91 : forall c,
  0 <= c <= 127 ->
  (ascii_of_z c = " "%char <-> c = 32).
Proof.
  intros c Hc. split.
  - intros H.
    apply (ascii_of_z_7bit_inj_91 c 32 Hc ltac:(lia)).
    exact H.
  - intros ->. reflexivity.
Qed.

Lemma ascii_of_z_i_91 : forall c,
  0 <= c <= 127 ->
  (ascii_of_z c = "I"%char <-> c = 73).
Proof.
  intros c Hc. split.
  - intros H.
    apply (ascii_of_z_7bit_inj_91 c 73 Hc ltac:(lia)).
    exact H.
  - intros ->. reflexivity.
Qed.

Lemma z_delimiter_ascii_91 : forall c,
  0 <= c <= 127 ->
  (z_sentence_delimiter_91 c <-> sentence_delimiter (ascii_of_z c)).
Proof.
  intros c Hc.
  unfold z_sentence_delimiter_91, sentence_delimiter.
  split.
  - intros [-> | [-> | ->]]; auto.
  - intros [H | [H | H]].
    + left. eapply ascii_of_z_7bit_inj_91; try eassumption; lia.
    + right; left. eapply ascii_of_z_7bit_inj_91; try eassumption; lia.
    + right; right. eapply ascii_of_z_7bit_inj_91; try eassumption; lia.
Qed.

Lemma z_sentence_start_ascii_91 : forall input start,
  all_ascii input ->
  (z_sentence_start_91 input start <->
   sentence_start (map ascii_of_z input) start).
Proof.
  intros input start Hall.
  unfold z_sentence_start_91, sentence_start.
  split.
  - intros [-> | (p & c & Hstart & Hnth & Hdelim)].
    + left; reflexivity.
    + right. exists p, (ascii_of_z c). repeat split; try assumption.
      * apply nth_error_map_ascii_of_z_91. eauto.
      * apply (proj1 (z_delimiter_ascii_91 c ltac:(
          eapply all_ascii_nth_error_91; eauto))). exact Hdelim.
  - intros [-> | (p & a & Hstart & Hnth & Hdelim)].
    + left; reflexivity.
    + apply nth_error_map_ascii_of_z_91 in Hnth.
      destruct Hnth as (c & Hnth & Hchar). subst a.
      right. exists p, c. repeat split; try assumption.
      apply (proj2 (z_delimiter_ascii_91 c ltac:(
        eapply all_ascii_nth_error_91; eauto))). exact Hdelim.
Qed.

Lemma z_begins_ascii_91 : forall input i,
  all_ascii input ->
  (z_begins_sentence_at_91 input i <->
   begins_sentence_at (map ascii_of_z input) i).
Proof.
  intros input i Hall.
  unfold z_begins_sentence_at_91, begins_sentence_at.
  split.
  - intros (start & Hstart & Hle & Hspaces).
    exists start. repeat split; try assumption.
    + apply (proj1 (z_sentence_start_ascii_91 input start Hall)); exact Hstart.
    + intros j Hj.
      apply nth_error_map_ascii_of_z_91.
      exists 32. split.
      * apply Hspaces; exact Hj.
      * reflexivity.
  - intros (start & Hstart & Hle & Hspaces).
    exists start. repeat split; try assumption.
    + apply (proj2 (z_sentence_start_ascii_91 input start Hall)); exact Hstart.
    + intros j Hj.
      specialize (Hspaces j Hj).
      apply nth_error_map_ascii_of_z_91 in Hspaces.
      destruct Hspaces as (c & Hnth & Hchar).
      assert (Hc : 0 <= c <= 127) by
        (eapply all_ascii_nth_error_91; eauto).
      apply ascii_of_z_space_91 in Hchar; auto.
      subst c; exact Hnth.
Qed.

Lemma z_boredom_ascii_91 : forall input i,
  all_ascii input ->
  (z_boredom_at_91 input i <->
   boredom_at (map ascii_of_z input) i).
Proof.
  intros input i Hall.
  unfold z_boredom_at_91, boredom_at.
  rewrite (z_begins_ascii_91 input i Hall).
  split.
  - intros (Hbegin & Hi & Hspace). repeat split; try assumption.
    + apply nth_error_map_ascii_of_z_91. exists 73. split.
      * exact Hi.
      * reflexivity.
    + apply nth_error_map_ascii_of_z_91. exists 32. split.
      * exact Hspace.
      * reflexivity.
  - intros (Hbegin & Hi & Hspace). repeat split; try assumption.
    + apply nth_error_map_ascii_of_z_91 in Hi.
      destruct Hi as (c & Hnth & Hchar).
      assert (Hc : 0 <= c <= 127) by
        (eapply all_ascii_nth_error_91; eauto).
      apply ascii_of_z_i_91 in Hchar; auto. subst; exact Hnth.
    + apply nth_error_map_ascii_of_z_91 in Hspace.
      destruct Hspace as (c & Hnth & Hchar).
      assert (Hc : 0 <= c <= 127) by
        (eapply all_ascii_nth_error_91; eauto).
      apply ascii_of_z_space_91 in Hchar; auto. subst; exact Hnth.
Qed.

Definition bored_follow_positions_91 (input : list Z) : list nat :=
  filter (fun j => bored_followb_91 j input)
    (seq 0 (List.length input)).

Definition bored_positions_91 (input : list Z) : list nat :=
  map Nat.pred (bored_follow_positions_91 input).

Lemma bored_followb_positive_91 : forall input j,
  bored_followb_91 j input = true ->
  j <> O.
Proof.
  intros input [| j] H; simpl in H; congruence.
Qed.

Lemma pred_injective_positive_91 : forall x y,
  x <> O -> y <> O -> Nat.pred x = Nat.pred y -> x = y.
Proof.
  intros [| x] [| y]; simpl; intros; try congruence.
Qed.

Lemma NoDup_map_pred_positive_91 : forall l,
  NoDup l ->
  (forall x, In x l -> x <> O) ->
  NoDup (map Nat.pred l).
Proof.
  intros l Hnodup.
  induction Hnodup as [| x l Hnotin Hnodup IH]; intros Hpositive; simpl.
  - constructor.
  - constructor.
    + intros Hin.
      apply in_map_iff in Hin.
      destruct Hin as (y & Hpred & Hyin).
      assert (Hxpos : x <> O) by (apply Hpositive; left; reflexivity).
      assert (Hypos : y <> O) by (apply Hpositive; right; exact Hyin).
      assert (x = y) by
        (eapply pred_injective_positive_91; eauto; symmetry; exact Hpred).
      subst y; contradiction.
    + apply IH. intros y Hy. apply Hpositive. right; exact Hy.
Qed.

Lemma bored_follow_positions_nodup_91 : forall input,
  NoDup (bored_follow_positions_91 input).
Proof.
  intros input. unfold bored_follow_positions_91.
  apply NoDup_filter. apply seq_NoDup.
Qed.

Lemma bored_positions_nodup_91 : forall input,
  NoDup (bored_positions_91 input).
Proof.
  intros input. unfold bored_positions_91.
  apply NoDup_map_pred_positive_91.
  - apply bored_follow_positions_nodup_91.
  - intros j Hj.
    unfold bored_follow_positions_91 in Hj.
    apply filter_In in Hj. destruct Hj as [_ Hfollow].
    eapply bored_followb_positive_91; eauto.
Qed.

Lemma bored_positions_z_spec_91 : forall input i,
  In i (bored_positions_91 input) <-> z_boredom_at_91 input i.
Proof.
  intros input i. unfold bored_positions_91, bored_follow_positions_91.
  split.
  - intros Hin. apply in_map_iff in Hin.
    destruct Hin as (j & Hpred & Hj).
    apply filter_In in Hj. destruct Hj as [Hseq Hfollow].
    apply in_seq in Hseq. destruct Hseq as [_ Hjbound].
    assert (Hjpos : j <> O) by
      (eapply bored_followb_positive_91; eauto).
    destruct j as [| j]; [contradiction |].
    simpl in Hpred. subst j.
    apply bored_followb_z_boredom_91; assumption.
  - intros Hbored.
    assert (Hnext : (S i < List.length input)%nat).
    { destruct Hbored as (_ & _ & Hspace).
      apply nth_error_Some. congruence. }
    apply in_map_iff. exists (S i). split; [reflexivity |].
    apply filter_In. split.
    + apply in_seq. lia.
    + apply (proj2 (bored_followb_z_boredom_91 input i Hnext)).
      exact Hbored.
Qed.

Lemma bored_positions_ascii_spec_91 : forall input i,
  all_ascii input ->
  (In i (bored_positions_91 input) <->
   boredom_at (map ascii_of_z input) i).
Proof.
  intros input i Hall.
  rewrite bored_positions_z_spec_91.
  apply z_boredom_ascii_91; exact Hall.
Qed.

Lemma bored_positions_length_91 : forall input,
  bored_sum_prefix_z (string_length input) input =
  Z.of_nat (List.length (bored_positions_91 input)).
Proof.
  intros input.
  unfold string_length, bored_positions_91, bored_follow_positions_91.
  rewrite Zlength_correct.
  rewrite bored_sum_filter_91.
  rewrite length_map. reflexivity.
Qed.

Lemma problem_91_from_bored_sum_91 : forall input,
  valid_string input ->
  problem_91_spec_z input
    (bored_sum_prefix_z (string_length input) input).
Proof.
  intros input [Hall _].
  unfold problem_91_spec_z, problem_91_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  exists (bored_positions_91 input). split.
  - apply bored_positions_nodup_91.
  - split.
    + intros i. apply bored_positions_ascii_spec_91; exact Hall.
    + rewrite bored_positions_length_91, Nat2Z.id; reflexivity.
Qed.
