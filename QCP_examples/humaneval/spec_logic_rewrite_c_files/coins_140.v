Load "../spec/140".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.
Load "../StringClaude/string_bridge".
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_140_pre_z (input : list Z) : Prop :=
  problem_140_pre (string_of_list_z input).

Definition problem_140_spec_z (input output : list Z) : Prop :=
  problem_140_spec (string_of_list_z input) (string_of_list_z output).

Definition flush_spaces_z_140 (n : Z) : list Z :=
  if Z.eq_dec n 0 then []
  else if Z.eq_dec n 1 then [95]
  else if Z.eq_dec n 2 then [95; 95]
  else [45].

Inductive scan_rel_z_140 : list Z -> list Z -> Z -> Prop :=
| scan_rel_z_140_nil : scan_rel_z_140 [] [] 0
| scan_rel_z_140_space : forall consumed output pending,
    0 <= pending ->
    scan_rel_z_140 consumed output pending ->
    scan_rel_z_140 (consumed ++ [32]) output (pending + 1)
| scan_rel_z_140_char : forall consumed output pending c,
    0 <= pending ->
    c <> 32 ->
    scan_rel_z_140 consumed output pending ->
    scan_rel_z_140
      (consumed ++ [c])
      (output ++ flush_spaces_z_140 pending ++ [c])
      0.

Definition fix_spaces_state_z_140
    (input output : list Z) (i pending : Z) : Prop :=
  0 <= i <= Zlength input /\
  0 <= pending <= i /\
  Zlength output + pending <= i /\
  scan_rel_z_140 (firstn (Z.to_nat i) input) output pending.

Lemma fix_spaces_state_z_140_init : forall input,
  fix_spaces_state_z_140 input [] 0 0.
Proof.
  intros input.
  unfold fix_spaces_state_z_140.
  repeat split; try lia; try apply Zlength_nonneg; try constructor; try reflexivity.
Qed.

Lemma firstn_succ_nth_140 : forall (l : list Z) n,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l 0].
Proof.
  induction l as [| x xs IH]; intros [| n] Hn; simpl in *.
  - lia.
  - lia.
  - reflexivity.
  - rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_z_succ_140 : forall (input : list Z) i,
  0 <= i < Zlength input ->
  firstn (Z.to_nat (i + 1)) input =
    firstn (Z.to_nat i) input ++ [Znth i input 0].
Proof.
  intros input i Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply firstn_succ_nth_140.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  exact (proj2 Hi).
Qed.

Lemma flush_spaces_z_140_length_le : forall pending,
  0 <= pending ->
  Zlength (flush_spaces_z_140 pending) <= pending.
Proof.
  intros pending Hp.
  unfold flush_spaces_z_140.
  destruct (Z.eq_dec pending 0) as [H0 | H0].
  - subst pending. reflexivity.
  - destruct (Z.eq_dec pending 1) as [H1 | H1].
    + subst pending. reflexivity.
    + destruct (Z.eq_dec pending 2) as [H2 | H2].
      * subst pending. reflexivity.
      * rewrite Zlength_cons, Zlength_nil. lia.
Qed.

Lemma fix_spaces_state_z_140_space : forall input output i pending,
  0 <= i < Zlength input ->
  Znth i (c_string input) 0 = 32 ->
  fix_spaces_state_z_140 input output i pending ->
  fix_spaces_state_z_140 input output (i + 1) (pending + 1).
Proof.
  intros input output i pending Hi Hspace Hstate.
  unfold fix_spaces_state_z_140 in *.
  destruct Hstate as [Hib [Hpb [Hlen Hscan]]].
  repeat split; try lia.
  rewrite firstn_z_succ_140 by lia.
  assert (Hinside : Znth i (c_string input) 0 = Znth i input 0).
  { apply c_string_Znth_inside. unfold string_length. lia. }
  rewrite Hinside in Hspace.
  rewrite Hspace.
  apply scan_rel_z_140_space; [lia | exact Hscan].
Qed.

Lemma fix_spaces_state_z_140_char : forall input output i pending,
  0 <= i < Zlength input ->
  Znth i (c_string input) 0 <> 32 ->
  fix_spaces_state_z_140 input output i pending ->
  fix_spaces_state_z_140 input
    (output ++ flush_spaces_z_140 pending ++
      [Znth i (c_string input) 0])
    (i + 1) 0.
Proof.
  intros input output i pending Hi Hchar Hstate.
  unfold fix_spaces_state_z_140 in *.
  destruct Hstate as [Hib [Hpb [Hlen Hscan]]].
  repeat split; try lia.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil.
    pose proof (flush_spaces_z_140_length_le pending ltac:(lia)).
    lia.
  - rewrite firstn_z_succ_140 by lia.
    assert (Hinside : Znth i (c_string input) 0 = Znth i input 0).
    { apply c_string_Znth_inside. unfold string_length. lia. }
    rewrite Hinside in Hchar |- *.
    apply scan_rel_z_140_char; [lia | exact Hchar | exact Hscan].
Qed.

Definition ends_non_space_140 (chunks : list (list ascii)) : Prop :=
  chunks = [] \/
  exists prefix last,
    chunks = prefix ++ [last] /\ non_space_chunk last.

Lemma non_space_chunk_singleton_140 : forall c,
  c <> space -> non_space_chunk [c].
Proof.
  intros c Hc. split; [discriminate | constructor; [exact Hc | constructor]].
Qed.

Lemma non_space_chunk_not_space_chunk_140 : forall chunk,
  non_space_chunk chunk -> ~ space_chunk chunk.
Proof.
  intros chunk [_ Hnon] (n & Hn & ->).
  destruct n as [| n]; [lia |].
  inversion Hnon as [| c rest Hc Hrest]; subst.
  apply Hc. reflexivity.
Qed.

Lemma no_adjacent_space_chunks_snoc_nonspace_140 : forall chunks chunk,
  no_adjacent_space_chunks chunks ->
  non_space_chunk chunk ->
  no_adjacent_space_chunks (chunks ++ [chunk]).
Proof.
  induction chunks as [| a rest IH]; intros chunk Hno Hchunk.
  - unfold no_adjacent_space_chunks. simpl. constructor.
  - destruct rest as [| b rest].
    + unfold no_adjacent_space_chunks. simpl.
      constructor.
      * intros [_ Hspace].
        exact (non_space_chunk_not_space_chunk_140 chunk Hchunk Hspace).
      * constructor.
    + unfold no_adjacent_space_chunks in Hno |- *.
      simpl in Hno |- *.
      inversion Hno as [| pair pairs Hhead Htail]; subst.
      constructor; [exact Hhead |].
      apply IH; assumption.
Qed.

Lemma ends_non_space_140_snoc_nonspace : forall chunks chunk,
  non_space_chunk chunk ->
  ends_non_space_140 (chunks ++ [chunk]).
Proof.
  intros chunks chunk Hchunk.
  right. exists chunks, chunk. auto.
Qed.

Lemma no_adjacent_space_chunks_snoc_space_140 : forall chunks chunk,
  no_adjacent_space_chunks chunks ->
  ends_non_space_140 chunks ->
  space_chunk chunk ->
  no_adjacent_space_chunks (chunks ++ [chunk]).
Proof.
  induction chunks as [| a rest IH]; intros chunk Hno Hend Hspace.
  - unfold no_adjacent_space_chunks. simpl. constructor.
  - destruct rest as [| b rest].
    + unfold ends_non_space_140 in Hend.
      destruct Hend as [Hnil | (prefix & last & Heq & Hlast)];
        [discriminate |].
      assert (a = last).
      { pose proof (f_equal (@List.length _) Heq) as Hlen.
        rewrite length_app in Hlen. simpl in Hlen.
        assert (prefix = []) by (apply length_zero_iff_nil; lia).
        subst prefix. simpl in Heq. inversion Heq. reflexivity. }
      subst last.
      unfold no_adjacent_space_chunks. simpl.
      constructor.
      * intros [Ha _].
        exact (non_space_chunk_not_space_chunk_140 a Hlast Ha).
      * constructor.
    + unfold no_adjacent_space_chunks in Hno |- *.
      simpl in Hno |- *.
      inversion Hno as [| pair pairs Hhead Htail]; subst.
      constructor; [exact Hhead |].
      apply IH.
      * exact Htail.
      * unfold ends_non_space_140 in *.
        destruct Hend as [Hnil | (prefix & last & Heq & Hlast)];
          [discriminate |].
        right.
        destruct prefix as [| p prefix].
        { simpl in Heq. discriminate. }
        exists prefix, last.
        simpl in Heq. injection Heq as _ HtailEq.
        split; [exact HtailEq | exact Hlast].
      * exact Hspace.
Qed.

Lemma repeat_ascii_snoc_140 : forall (c : ascii) n,
  repeat c (S n) = repeat c n ++ [c].
Proof.
  intros c n. induction n; [reflexivity |].
  simpl. f_equal. exact IHn.
Qed.

Lemma ascii_of_z_32_140 : ascii_of_z 32 = space.
Proof. reflexivity. Qed.

Lemma ascii_of_z_95_140 : ascii_of_z 95 = underscore.
Proof. reflexivity. Qed.

Lemma ascii_of_z_45_140 : ascii_of_z 45 = dash.
Proof. reflexivity. Qed.

Lemma flush_spaces_chunk_140 : forall pending,
  0 < pending ->
  fix_spaces_chunk
    (repeat space (Z.to_nat pending))
    (map ascii_of_z (flush_spaces_z_140 pending)).
Proof.
  intros pending Hp.
  unfold flush_spaces_z_140, fix_spaces_chunk.
  destruct (Z.eq_dec pending 0) as [H0 | H0]; [lia |].
  destruct (Z.eq_dec pending 1) as [H1 | H1].
  - subst pending. right. left.
    exists 1%nat. simpl. repeat split; try lia; reflexivity.
  - destruct (Z.eq_dec pending 2) as [H2 | H2].
    + subst pending. right. left.
      exists 2%nat. simpl. repeat split; try lia; reflexivity.
    + right. right.
      exists (Z.to_nat pending).
      repeat split; try reflexivity.
      lia.
Qed.

Lemma all_ascii_Forall_140 : forall l,
  string_lib.all_ascii l ->
  Forall (fun c => 0 <= c <= 127) l.
Proof.
  intros l Hall.
  apply Forall_forall.
  intros c Hc.
  destruct (In_nth l c 0 Hc) as [n [Hn Hnth]].
  specialize (Hall (Z.of_nat n)).
  unfold Znth in Hall.
  rewrite Nat2Z.id in Hall.
  rewrite Hnth in Hall.
  apply Hall.
  rewrite Zlength_correct. lia.
Qed.

Definition scan_chunks_inv_140
    (consumed output : list Z) (pending : Z) : Prop :=
  exists input_chunks output_chunks,
    Forall2 fix_spaces_chunk input_chunks output_chunks /\
    no_adjacent_space_chunks input_chunks /\
    List.concat input_chunks ++ repeat space (Z.to_nat pending) =
      map ascii_of_z consumed /\
    List.concat output_chunks = map ascii_of_z output /\
    ends_non_space_140 input_chunks.

Lemma scan_rel_chunks_140 : forall consumed output pending,
  scan_rel_z_140 consumed output pending ->
  Forall (fun c => 0 <= c <= 127) consumed ->
  scan_chunks_inv_140 consumed output pending.
Proof.
  intros consumed output pending Hscan.
  induction Hscan as
      [| consumed output pending Hp Hscan IH
       | consumed output pending c Hp Hc Hscan IH];
    intros Hcodes.
  - exists [], [].
    repeat split; try constructor; reflexivity.
  - rewrite Forall_app in Hcodes.
    destruct Hcodes as [Hcodes _].
    destruct (IH Hcodes) as
      (input_chunks & output_chunks & Hrel & Hno & Hin & Hout & Hend).
    exists input_chunks, output_chunks.
    repeat split; try assumption.
    replace (Z.to_nat (pending + 1)) with (S (Z.to_nat pending)) by lia.
    rewrite repeat_ascii_snoc_140, map_app. simpl.
    rewrite ascii_of_z_32_140.
    rewrite app_assoc, Hin. reflexivity.
  - rewrite Forall_app in Hcodes.
    destruct Hcodes as [Hcodes Hcode].
    inversion Hcode as [| ac tail Hcrange _]; subst.
    destruct (IH Hcodes) as
      (input_chunks & output_chunks & Hrel & Hno & Hin & Hout & Hend).
    assert (Hascii_ne : ascii_of_z c <> space).
    { intro Heq.
      change (ascii_of_z c = ascii_of_z 32) in Heq.
      apply (f_equal nat_of_ascii) in Heq.
      rewrite !nat_of_ascii_ascii_of_z in Heq by lia.
      lia. }
    pose proof (non_space_chunk_singleton_140
      (ascii_of_z c) Hascii_ne) as Hnon.
    destruct (Z.eq_dec pending 0) as [Hpending0 | Hpending0].
    + subst pending.
      exists (input_chunks ++ [[ascii_of_z c]]),
        (output_chunks ++ [[ascii_of_z c]]).
      repeat split.
      * apply Forall2_app; [exact Hrel |]. constructor; [|constructor].
        left. split; [exact Hnon | reflexivity].
      * apply no_adjacent_space_chunks_snoc_nonspace_140; assumption.
      * rewrite !List.concat_app. simpl.
        simpl in Hin. rewrite app_nil_r in Hin.
        rewrite map_app. simpl. rewrite !app_nil_r, <- Hin. reflexivity.
      * rewrite !List.concat_app. simpl.
        unfold flush_spaces_z_140. simpl.
        rewrite map_app. simpl. rewrite <- Hout. reflexivity.
      * apply ends_non_space_140_snoc_nonspace. exact Hnon.
    + assert (Hpositive : 0 < pending) by lia.
      set (space_run := repeat space (Z.to_nat pending)).
      set (space_out := map ascii_of_z (flush_spaces_z_140 pending)).
      exists (input_chunks ++ [space_run; [ascii_of_z c]]),
        (output_chunks ++ [space_out; [ascii_of_z c]]).
      repeat split.
      * apply Forall2_app; [exact Hrel |].
        constructor.
        -- subst space_run space_out.
           apply flush_spaces_chunk_140. exact Hpositive.
        -- constructor.
           ++ left. split; [exact Hnon | reflexivity].
           ++ constructor.
      * replace (input_chunks ++ [space_run; [ascii_of_z c]])
          with ((input_chunks ++ [space_run]) ++ [[ascii_of_z c]])
          by (rewrite <- app_assoc; reflexivity).
        apply no_adjacent_space_chunks_snoc_nonspace_140; [|exact Hnon].
        apply no_adjacent_space_chunks_snoc_space_140; try assumption.
        subst space_run. exists (Z.to_nat pending).
        split; [lia | reflexivity].
      * rewrite !List.concat_app. simpl.
        subst space_run.
        rewrite !map_app. simpl.
        rewrite !app_nil_r, app_assoc, Hin. reflexivity.
      * rewrite !List.concat_app. simpl.
        subst space_out.
        rewrite !map_app. simpl.
        rewrite Hout. reflexivity.
      * replace (input_chunks ++ [space_run; [ascii_of_z c]])
          with ((input_chunks ++ [space_run]) ++ [[ascii_of_z c]])
          by (rewrite <- app_assoc; reflexivity).
        apply ends_non_space_140_snoc_nonspace. exact Hnon.
Qed.

Lemma problem_140_spec_z_from_state : forall input prefix pending output,
  valid_string input ->
  fix_spaces_state_z_140 input prefix (Zlength input) pending ->
  output = prefix ++ flush_spaces_z_140 pending ->
  problem_140_spec_z input output.
Proof.
  intros input prefix pending output Hvalid Hstate Houtput.
  unfold fix_spaces_state_z_140 in Hstate.
  destruct Hstate as [_ [Hpending [_ Hscan]]].
  assert (Hfirstn : firstn (Z.to_nat (Zlength input)) input = input).
  { rewrite z_to_nat_Zlength. apply firstn_all. }
  rewrite Hfirstn in Hscan.
  destruct Hvalid as [Hascii Hnonul].
  pose proof (all_ascii_Forall_140 input Hascii) as Hcodes.
  destruct (scan_rel_chunks_140 input prefix pending Hscan Hcodes) as
    (input_chunks & output_chunks & Hrel & Hno & Hin & Hout & Hend).
  unfold problem_140_spec_z, problem_140_spec.
  rewrite !list_ascii_of_string_string_of_list_z.
  destruct (Z.eq_dec pending 0) as [Hpending0 | Hpending0].
  - subst pending.
    exists input_chunks, output_chunks.
    repeat split; try assumption.
    + simpl in Hin. rewrite app_nil_r in Hin. exact Hin.
    + subst output. unfold flush_spaces_z_140. simpl.
      rewrite app_nil_r.
      exact Hout.
  - assert (Hpositive : 0 < pending) by lia.
    set (space_run := repeat space (Z.to_nat pending)).
    set (space_out := map ascii_of_z (flush_spaces_z_140 pending)).
    exists (input_chunks ++ [space_run]), (output_chunks ++ [space_out]).
    repeat split.
    + apply Forall2_app; [exact Hrel |].
      constructor; [|constructor].
      subst space_run space_out.
      apply flush_spaces_chunk_140. exact Hpositive.
    + apply no_adjacent_space_chunks_snoc_space_140; try assumption.
      subst space_run. exists (Z.to_nat pending).
      split; [lia | reflexivity].
    + rewrite List.concat_app. simpl. subst space_run.
      rewrite app_nil_r. exact Hin.
    + rewrite List.concat_app. simpl. subst space_out.
      rewrite app_nil_r.
      subst output. rewrite !map_app.
      rewrite Hout. reflexivity.
Qed.
