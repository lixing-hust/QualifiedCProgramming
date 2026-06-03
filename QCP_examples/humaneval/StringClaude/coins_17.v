Load "../spec/17".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_17_pre_z (input : list Z) : Prop :=
  problem_17_pre (string_of_list_z input).

Definition problem_17_spec_z (input output : list Z) : Prop :=
  problem_17_spec (string_of_list_z input) (map Z.to_nat output).

Definition ascii_range_z (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition note_state_step_z (state ch : Z) : Z :=
  if Z.eqb ch 32 then 0
  else if Z.eqb state 0 then
    if Z.eqb ch 111 then 1
    else if Z.eqb ch 46 then 3
    else 5
  else if Z.eqb state 1 then
    if Z.eqb ch 124 then 2 else 5
  else if Z.eqb state 3 then
    if Z.eqb ch 124 then 4 else 5
  else 5.

Definition music_step_state_z : Z -> Z -> Z := note_state_step_z.

Definition music_final_output_z (out : list Z) (state : Z) : list Z :=
  if Z.eqb state 1 then out ++ [4]
  else if Z.eqb state 2 then out ++ [2]
  else if Z.eqb state 4 then out ++ [1]
  else out.

Definition music_step_output_z (out : list Z) (state ch : Z) : list Z :=
  if Z.eqb ch 32 then music_final_output_z out state else out.

Fixpoint music_scan_aux (chars out : list Z) (state : Z) : list Z * Z :=
  match chars with
  | [] => (out, state)
  | ch :: rest =>
      music_scan_aux rest
        (music_step_output_z out state ch)
        (note_state_step_z state ch)
  end.

Definition music_prefix_output_z (i : Z) (input : list Z) : list Z :=
  fst (music_scan_aux (sublist 0 i input) [] 0).

Definition music_prefix_state_z (i : Z) (input : list Z) : Z :=
  snd (music_scan_aux (sublist 0 i input) [] 0).

Definition music_output_z (input : list Z) : list Z :=
  let scanned := music_scan_aux input [] 0 in
  music_final_output_z (fst scanned) (snd scanned).

Lemma music_prefix_full_final : forall input len,
  len = Zlength input ->
  music_final_output_z
    (music_prefix_output_z len input)
    (music_prefix_state_z len input) =
  music_output_z input.
Proof.
  intros input len Hlen.
  unfold music_prefix_output_z, music_prefix_state_z, music_output_z.
  rewrite (sublist_self input len Hlen).
  reflexivity.
Qed.

Lemma music_scan_aux_step : forall prefix ch out state,
  music_scan_aux (prefix ++ [ch]) out state =
  let scanned := music_scan_aux prefix out state in
  (music_step_output_z (fst scanned) (snd scanned) ch,
   note_state_step_z (snd scanned) ch).
Proof.
  induction prefix as [| h t IH]; intros ch out state; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma music_prefix_step : forall input i,
  0 <= i < Zlength input ->
  music_prefix_output_z (i + 1) input =
    music_step_output_z
      (music_prefix_output_z i input)
      (music_prefix_state_z i input)
      (Znth i input 0) /\
  music_prefix_state_z (i + 1) input =
    note_state_step_z
      (music_prefix_state_z i input)
      (Znth i input 0).
Proof.
  intros input i Hi.
  unfold music_prefix_output_z, music_prefix_state_z.
  assert (sublist 0 (i + 1) input = sublist 0 i input ++ [Znth i input 0]) as Hsub.
  {
    rewrite (sublist_split 0 (i + 1) i input);
      [| lia | rewrite <- Zlength_correct; lia].
    rewrite (sublist_single i input 0) by (rewrite <- Zlength_correct; lia).
    reflexivity.
  }
  rewrite Hsub.
  rewrite music_scan_aux_step.
  split; reflexivity.
Qed.

Lemma music_prefix_step_app : forall input i,
  0 <= i < Zlength input ->
  music_prefix_output_z (i + 1) input =
    music_step_output_z
      (music_prefix_output_z i input)
      (music_prefix_state_z i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  music_prefix_state_z (i + 1) input =
    note_state_step_z
      (music_prefix_state_z i input)
      (Znth i (app input (cons 0 nil)) 0).
Proof.
  intros input i Hi.
  pose proof (music_prefix_step input i Hi) as [Hout Hstate].
  replace (Znth i (app input (cons 0 nil)) 0) with (Znth i input 0).
  - split; assumption.
  - rewrite app_Znth1; lia.
Qed.

Lemma note_state_step_range : forall state ch,
  0 <= state <= 5 ->
  0 <= note_state_step_z state ch <= 5.
Proof.
  intros state ch Hstate.
  unfold note_state_step_z.
  destruct (Z.eqb ch 32) eqn:?; [lia |].
  destruct (Z.eqb state 0) eqn:?.
  - destruct (Z.eqb ch 111) eqn:?; [lia |].
    destruct (Z.eqb ch 46) eqn:?; lia.
  - destruct (Z.eqb state 1) eqn:?.
    + destruct (Z.eqb ch 124) eqn:?; lia.
    + destruct (Z.eqb state 3) eqn:?.
      * destruct (Z.eqb ch 124) eqn:?; lia.
      * lia.
Qed.

Lemma music_step_space_skip : forall out state,
  state <> 1 -> state <> 2 -> state <> 4 ->
  music_step_output_z out state 32 = out /\
  note_state_step_z state 32 = 0.
Proof.
  intros out state H1 H2 H4.
  unfold music_step_output_z, music_final_output_z, note_state_step_z.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq state 1) H1).
  rewrite (proj2 (Z.eqb_neq state 2) H2).
  rewrite (proj2 (Z.eqb_neq state 4) H4).
  split; reflexivity.
Qed.

Lemma music_step_space_1 : forall out,
  music_step_output_z out 1 32 = out ++ [4] /\
  note_state_step_z 1 32 = 0.
Proof.
  intros out.
  unfold music_step_output_z, music_final_output_z, note_state_step_z.
  repeat rewrite Z.eqb_refl.
  split; reflexivity.
Qed.

Lemma music_step_space_2 : forall out,
  music_step_output_z out 2 32 = out ++ [2] /\
  note_state_step_z 2 32 = 0.
Proof.
  intros out.
  unfold music_step_output_z, music_final_output_z, note_state_step_z.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 2 1) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_space_4 : forall out,
  music_step_output_z out 4 32 = out ++ [1] /\
  note_state_step_z 4 32 = 0.
Proof.
  intros out.
  unfold music_step_output_z, music_final_output_z, note_state_step_z.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 4 1) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 4 2) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_0_o : forall out,
  music_step_output_z out 0 111 = out /\
  note_state_step_z 0 111 = 1.
Proof.
  intros out.
  unfold music_step_output_z, note_state_step_z.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 111 32) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_0_dot : forall out,
  music_step_output_z out 0 46 = out /\
  note_state_step_z 0 46 = 3.
Proof.
  intros out.
  unfold music_step_output_z, note_state_step_z.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 46 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 46 111) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_1_bar : forall out,
  music_step_output_z out 1 124 = out /\
  note_state_step_z 1 124 = 2.
Proof.
  intros out.
  unfold music_step_output_z, note_state_step_z.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 124 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_3_bar : forall out,
  music_step_output_z out 3 124 = out /\
  note_state_step_z 3 124 = 4.
Proof.
  intros out.
  unfold music_step_output_z, note_state_step_z.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 124 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 1) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_3_bad : forall out ch,
  ch <> 32 -> ch <> 124 ->
  music_step_output_z out 3 ch = out /\
  note_state_step_z 3 ch = 5.
Proof.
  intros out ch Hspace Hbar.
  unfold music_step_output_z, note_state_step_z.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq 3 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 1) ltac:(lia)).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 124) Hbar).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_1_bad : forall out ch,
  ch <> 32 -> ch <> 124 ->
  music_step_output_z out 1 ch = out /\
  note_state_step_z 1 ch = 5.
Proof.
  intros out ch Hspace Hbar.
  unfold music_step_output_z, note_state_step_z.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 124) Hbar).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_0_bad : forall out ch,
  ch <> 32 -> ch <> 111 -> ch <> 46 ->
  music_step_output_z out 0 ch = out /\
  note_state_step_z 0 ch = 5.
Proof.
  intros out ch Hspace Ho Hdot.
  unfold music_step_output_z, note_state_step_z.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 111) Ho).
  rewrite (proj2 (Z.eqb_neq ch 46) Hdot).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_other_bad : forall out state ch,
  ch <> 32 -> state <> 0 -> state <> 1 -> state <> 3 ->
  music_step_output_z out state ch = out /\
  note_state_step_z state ch = 5.
Proof.
  intros out state ch Hspace H0 H1 H3.
  unfold music_step_output_z, note_state_step_z.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq state 0) H0).
  rewrite (proj2 (Z.eqb_neq state 1) H1).
  rewrite (proj2 (Z.eqb_neq state 3) H3).
  split; reflexivity.
Qed.

Lemma music_final_output_len_le : forall out state,
  0 <= state <= 5 ->
  Zlength (music_final_output_z out state) <= Zlength out + 1.
Proof.
  intros out state Hstate.
  unfold music_final_output_z.
  destruct (Z.eqb state 1) eqn:?.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - destruct (Z.eqb state 2) eqn:?.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + destruct (Z.eqb state 4) eqn:?.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * lia.
Qed.

Lemma music_step_output_len_le : forall out state ch,
  0 <= state <= 5 ->
  Zlength (music_step_output_z out state ch) <= Zlength out + 1.
Proof.
  intros out state ch Hstate.
  unfold music_step_output_z.
  destruct (Z.eqb ch 32) eqn:Hspace.
  - apply music_final_output_len_le; assumption.
  - lia.
Qed.

Lemma music_scan_aux_state_range : forall chars out state,
  0 <= state <= 5 ->
  0 <= snd (music_scan_aux chars out state) <= 5.
Proof.
  induction chars as [| ch rest IH]; intros out state Hstate; simpl.
  - exact Hstate.
  - apply IH.
    apply note_state_step_range.
    exact Hstate.
Qed.

Lemma music_prefix_state_range : forall input i,
  0 <= i <= Zlength input ->
  0 <= music_prefix_state_z i input <= 5.
Proof.
  intros input i Hi.
  unfold music_prefix_state_z.
  apply music_scan_aux_state_range.
  lia.
Qed.

Lemma music_scan_aux_output_len_le : forall chars out state,
  0 <= state <= 5 ->
  Zlength (fst (music_scan_aux chars out state)) <= Zlength out + Zlength chars.
Proof.
  induction chars as [| ch rest IH]; intros out state Hstate; simpl.
  - rewrite Zlength_nil. lia.
  - specialize (IH (music_step_output_z out state ch)
                  (note_state_step_z state ch)
                  (note_state_step_range state ch Hstate)).
    pose proof (music_step_output_len_le out state ch Hstate).
    rewrite Zlength_cons.
    lia.
Qed.

Lemma music_prefix_output_len_le : forall input i,
  0 <= i <= Zlength input ->
  Zlength (music_prefix_output_z i input) <= i.
Proof.
  intros input i Hi.
  unfold music_prefix_output_z.
  pose proof (music_scan_aux_output_len_le (sublist 0 i input) [] 0 ltac:(lia)) as Hlen.
  rewrite Zlength_nil in Hlen.
  rewrite Zlength_sublist0 in Hlen by lia.
  lia.
Qed.

Lemma music_final_output_len_bound : forall input,
  Zlength (music_output_z input) <= Zlength input + 1.
Proof.
  intros input.
  unfold music_output_z.
  pose proof (music_scan_aux_output_len_le input [] 0 ltac:(lia)) as Hscan.
  pose proof (music_final_output_len_le
    (fst (music_scan_aux input [] 0))
    (snd (music_scan_aux input [] 0))) as Hfinal.
  assert (0 <= snd (music_scan_aux input [] 0) <= 5) as H.
  { apply music_scan_aux_state_range. lia. }
  specialize (Hfinal H).
  rewrite Zlength_nil in Hscan.
  lia.
Qed.

Fixpoint list_z_of_ascii (l : list ascii) : list Z :=
  match l with
  | [] => []
  | c :: rest => Z.of_nat (nat_of_ascii c) :: list_z_of_ascii rest
  end.

Definition z_of_note_state (state : Z) : option Z :=
  if Z.eqb state 1 then Some 4
  else if Z.eqb state 2 then Some 2
  else if Z.eqb state 4 then Some 1
  else None.

Definition token_state_rev_z (current_group : list Z) : Z :=
  fold_left note_state_step_z (rev current_group) 0.

Definition token_output_z (current_group : list Z) : list Z :=
  music_final_output_z [] (token_state_rev_z current_group).

Fixpoint split_music_z_aux (current_group input : list Z) : list Z :=
  match input with
  | [] => token_output_z current_group
  | ch :: rest =>
      if Z.eqb ch 32 then
        token_output_z current_group ++ split_music_z_aux [] rest
      else
        split_music_z_aux (ch :: current_group) rest
  end.

Definition parse_note_output_nat (note : string) : list nat :=
  match parse_note note with
  | Some n => [n]
  | None => []
  end.

Definition no_space_z_list (l : list Z) : Prop :=
  forall ch, In ch l -> ch <> 32.

Lemma token_state_rev_z_cons : forall current_group ch,
  token_state_rev_z (ch :: current_group) =
  note_state_step_z (token_state_rev_z current_group) ch.
Proof.
  intros current_group ch.
  unfold token_state_rev_z.
  simpl.
  rewrite fold_left_app.
  reflexivity.
Qed.

Lemma music_final_output_app_17 : forall out state,
  music_final_output_z out state =
  out ++ music_final_output_z [] state.
Proof.
  intros out state.
  unfold music_final_output_z.
  destruct (Z.eqb state 1); simpl.
  - reflexivity.
  - destruct (Z.eqb state 2); simpl.
    + reflexivity.
    + destruct (Z.eqb state 4); simpl; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma music_scan_aux_split_final : forall input out current_group,
  music_final_output_z
    (fst (music_scan_aux input out (token_state_rev_z current_group)))
    (snd (music_scan_aux input out (token_state_rev_z current_group))) =
  out ++ split_music_z_aux current_group input.
Proof.
  induction input as [| ch rest IH]; intros out current_group; simpl.
  - unfold token_output_z.
    apply music_final_output_app_17.
  - destruct (Z.eqb ch 32) eqn:Hspace.
    + specialize (IH (music_final_output_z out (token_state_rev_z current_group)) []).
      unfold music_step_output_z in IH.
      unfold music_step_output_z.
      rewrite Hspace.
      unfold note_state_step_z.
      rewrite Hspace.
      change (token_state_rev_z []) with 0 in IH.
      change (token_state_rev_z []) with 0.
      rewrite IH.
      rewrite music_final_output_app_17.
      rewrite app_assoc.
      reflexivity.
    + rewrite <- token_state_rev_z_cons.
      specialize (IH out (ch :: current_group)).
      unfold music_step_output_z in IH.
      unfold music_step_output_z.
      rewrite Hspace.
      exact IH.
Qed.

Lemma music_output_split_music_z_aux : forall input,
  music_output_z input = split_music_z_aux [] input.
Proof.
  intros input.
  unfold music_output_z.
  pose proof (music_scan_aux_split_final input [] []) as Hout.
  change (token_state_rev_z []) with 0 in Hout.
  rewrite Hout.
  simpl.
  reflexivity.
Qed.

Lemma ascii_of_z_inj_range_17 : forall x y,
  0 <= x <= 127 ->
  0 <= y <= 127 ->
  ascii_of_z x = ascii_of_z y ->
  x = y.
Proof.
  intros x y Hx Hy H.
  apply (f_equal nat_of_ascii) in H.
  rewrite !nat_of_ascii_ascii_of_z in H by lia.
  lia.
Qed.

Lemma ascii_of_z_32_17 : ascii_of_z 32 = " "%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_46_17 : ascii_of_z 46 = "."%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_111_17 : ascii_of_z 111 = "o"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_124_17 : ascii_of_z 124 = "|"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_space_iff_17 : forall ch,
  0 <= ch <= 127 ->
  (ascii_of_z ch = " "%char <-> ch = 32).
Proof.
  intros ch Hch.
  split; intro H.
  - rewrite <- ascii_of_z_32_17 in H.
    apply ascii_of_z_inj_range_17 in H; [exact H | lia | lia].
  - subst. apply ascii_of_z_32_17.
Qed.

Lemma ascii_range_z_cons_inv : forall ch rest,
  ascii_range_z (ch :: rest) ->
  0 <= ch <= 127 /\ ascii_range_z rest.
Proof.
  intros ch rest Hrange.
  split.
  - specialize (Hrange 0 ltac:(rewrite Zlength_correct; simpl; lia)).
    simpl in Hrange.
    exact Hrange.
  - intros i Hi.
    specialize (Hrange (i + 1)).
    simpl in Hrange.
    rewrite Znth_cons in Hrange by lia.
    replace (i + 1 - 1) with i in Hrange by lia.
    apply Hrange.
    rewrite Zlength_correct in *; simpl in *.
    lia.
Qed.

Lemma ascii_range_z_tail : forall ch rest,
  ascii_range_z (ch :: rest) ->
  ascii_range_z rest.
Proof.
  intros ch rest Hrange.
  apply ascii_range_z_cons_inv in Hrange.
  tauto.
Qed.

Lemma ascii_range_z_head : forall ch rest,
  ascii_range_z (ch :: rest) ->
  0 <= ch <= 127.
Proof.
  intros ch rest Hrange.
  apply ascii_range_z_cons_inv in Hrange.
  tauto.
Qed.

Lemma ascii_range_z_rev_cons : forall ch current_group,
  0 <= ch <= 127 ->
  ascii_range_z (rev current_group) ->
  ascii_range_z (rev (ch :: current_group)).
Proof.
  intros ch current_group Hch Hcur.
  simpl.
  intros i Hi.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  destruct (Z_lt_ge_dec i (Zlength (rev current_group))).
  - rewrite app_Znth1 by lia.
    apply Hcur; lia.
  - rewrite app_Znth2 by lia.
    replace (i - Zlength (rev current_group)) with 0 by lia.
    simpl.
    exact Hch.
Qed.

Ltac solve_ascii_neq_17 :=
  match goal with
  | Hrange : 0 <= ?x <= 127, H : ascii_of_z ?x = ascii_of_z ?y |- _ =>
      apply ascii_of_z_inj_range_17 in H; try lia; subst; lia
  | Hrange : 0 <= ?x <= 127, H : ascii_of_z ?x = " "%char |- _ =>
      rewrite <- ascii_of_z_32_17 in H;
      apply ascii_of_z_inj_range_17 in H; try lia; subst; lia
  | Hrange : 0 <= ?x <= 127, H : ascii_of_z ?x = "o"%char |- _ =>
      rewrite <- ascii_of_z_111_17 in H;
      apply ascii_of_z_inj_range_17 in H; try lia; subst; lia
  | Hrange : 0 <= ?x <= 127, H : ascii_of_z ?x = "."%char |- _ =>
      rewrite <- ascii_of_z_46_17 in H;
      apply ascii_of_z_inj_range_17 in H; try lia; subst; lia
  | Hrange : 0 <= ?x <= 127, H : ascii_of_z ?x = "|"%char |- _ =>
      rewrite <- ascii_of_z_124_17 in H;
      apply ascii_of_z_inj_range_17 in H; try lia; subst; lia
  end.

Local Opaque string_dec.

Lemma note_state_step_5_nonspace_17 : forall ch,
  ch <> 32 ->
  note_state_step_z 5 ch = 5.
Proof.
  intros ch Hch.
  unfold note_state_step_z.
  rewrite (proj2 (Z.eqb_neq ch 32) Hch).
  reflexivity.
Qed.

Lemma fold_left_state_5_nonspace_17 : forall chars,
  no_space_z_list chars ->
  fold_left note_state_step_z chars 5 = 5.
Proof.
  induction chars as [| ch rest IH]; intros Hnospace; simpl.
  - reflexivity.
  - rewrite note_state_step_5_nonspace_17.
    + apply IH.
      intros x Hin. apply Hnospace. right. exact Hin.
    + apply Hnospace. left. reflexivity.
Qed.

Lemma fold_left_token_long_state_5_17 : forall chars,
  (3 <= List.length chars)%nat ->
  no_space_z_list chars ->
  fold_left note_state_step_z chars 0 = 5.
Proof.
  intros chars Hlen Hnospace.
  destruct chars as [| a [| b [| c rest]]]; simpl in Hlen; try lia.
  simpl.
  assert (Hthree :
    note_state_step_z (note_state_step_z (note_state_step_z 0 a) b) c = 5).
  {
    unfold note_state_step_z.
    repeat
      match goal with
      | |- context[Z.eqb a ?y] =>
          destruct (Z.eqb_spec a y); subst; simpl;
          try solve [exfalso; apply (Hnospace 32); simpl; tauto]
      | |- context[Z.eqb b ?y] =>
          destruct (Z.eqb_spec b y); subst; simpl;
          try solve [exfalso; apply (Hnospace 32); simpl; tauto]
      | |- context[Z.eqb c ?y] =>
          destruct (Z.eqb_spec c y); subst; simpl;
          try solve [exfalso; apply (Hnospace 32); simpl; tauto]
      end;
      reflexivity.
  }
  rewrite Hthree.
  apply fold_left_state_5_nonspace_17.
  intros x Hin; apply Hnospace; repeat right; exact Hin.
Qed.

Lemma parse_note_output_nat_len_ge3_17 : forall chars,
  (3 <= List.length chars)%nat ->
  parse_note_output_nat (string_of_list_ascii chars) = [].
Proof.
  intros chars Hlen.
  destruct chars as [| a [| b [| c rest]]]; simpl in Hlen; try lia.
  unfold parse_note_output_nat, parse_note.
  simpl.
  destruct (string_dec (String a (String b (String c (string_of_list_ascii rest)))) "o");
    [discriminate |].
  destruct (string_dec (String a (String b (String c (string_of_list_ascii rest)))) "o|");
    [discriminate |].
  destruct (string_dec (String a (String b (String c (string_of_list_ascii rest)))) ".|");
    [discriminate | reflexivity].
Qed.

Lemma token_output_parse_note_17 : forall current_group,
  ascii_range_z (rev current_group) ->
  no_space_z_list current_group ->
  map Z.to_nat (token_output_z current_group) =
    parse_note_output_nat
      (string_of_list_ascii (rev (map ascii_of_z current_group))).
Proof.
  intros current_group Hrange Hnospace.
  destruct current_group as [| c1 [| c2 [| c3 rest]]]; simpl in *.
  - reflexivity.
  - specialize (Hrange 0 ltac:(rewrite Zlength_cons, Zlength_nil; lia)) as Hc1.
    unfold token_output_z, token_state_rev_z, music_final_output_z,
      note_state_step_z, parse_note_output_nat, parse_note; simpl.
    destruct (Z.eqb_spec c1 32).
    { exfalso. apply (Hnospace c1); [left; reflexivity | assumption]. }
    destruct (Z.eqb_spec c1 111); [subst; reflexivity |].
    destruct (Z.eqb_spec c1 46); [subst |].
    + destruct (string_dec "." "o"); [congruence |].
      destruct (string_dec "." "o|"); [congruence |].
      destruct (string_dec "." ".|"); [congruence | reflexivity].
    + destruct (string_dec (String (ascii_of_z c1) EmptyString) "o") as [Hs | Hs].
      * injection Hs as Hchar.
        rewrite <- ascii_of_z_111_17 in Hchar.
        assert (c1 = 111) as ->.
        { apply ascii_of_z_inj_range_17; [exact Hc1 | lia | exact Hchar]. }
        contradiction.
      * destruct (string_dec (String (ascii_of_z c1) EmptyString) "o|") as [Ht | Ht].
        { discriminate Ht. }
        destruct (string_dec (String (ascii_of_z c1) EmptyString) ".|") as [Hu | Hu].
        { discriminate Hu. }
        reflexivity.
  - assert (Hc2 : 0 <= c2 <= 127).
    { specialize (Hrange 0 ltac:(rewrite Zlength_correct; simpl; lia)).
      simpl in Hrange.
      exact Hrange. }
    assert (Hc1 : 0 <= c1 <= 127).
    { specialize (Hrange 1 ltac:(rewrite Zlength_correct; simpl; lia)).
      rewrite Znth_cons in Hrange by lia.
      replace (1 - 1) with 0 in Hrange by lia.
      simpl in Hrange. exact Hrange. }
    unfold token_output_z, token_state_rev_z, music_final_output_z,
      note_state_step_z, parse_note_output_nat, parse_note; simpl.
    repeat rewrite ascii_of_z_32_17.
    repeat rewrite ascii_of_z_46_17.
    repeat rewrite ascii_of_z_111_17.
    repeat rewrite ascii_of_z_124_17.
    repeat rewrite Z.eqb_refl.
    destruct (Z.eqb_spec c2 32).
    { exfalso. apply (Hnospace c2); [right; left; reflexivity | assumption]. }
    destruct (Z.eqb_spec c2 111); subst.
    + change (ascii_of_z 111) with "o"%char.
      simpl.
      destruct (Z.eqb_spec c1 32).
      { exfalso. apply (Hnospace c1); [left; reflexivity | assumption]. }
      destruct (Z.eqb_spec c1 124); subst.
      * reflexivity.
      * destruct (string_dec (String "o"%char (String (ascii_of_z c1) EmptyString)) "o") as [Hs | Hs].
        { discriminate Hs. }
        destruct (string_dec (String "o"%char (String (ascii_of_z c1) EmptyString)) "o|") as [Ht | Ht].
        { inversion Ht; subst; solve_ascii_neq_17. }
        destruct (string_dec (String "o"%char (String (ascii_of_z c1) EmptyString)) ".|") as [Hu | Hu].
        { discriminate Hu. }
        reflexivity.
    + destruct (Z.eqb_spec c2 46); subst.
      * change (ascii_of_z 46) with "."%char.
        simpl.
        destruct (Z.eqb_spec c1 32).
        { exfalso. apply (Hnospace c1); [left; reflexivity | assumption]. }
        destruct (Z.eqb_spec c1 124); subst.
        { reflexivity. }
        destruct (string_dec (String "."%char (String (ascii_of_z c1) EmptyString)) "o") as [Hs | Hs].
        { discriminate Hs. }
        destruct (string_dec (String "."%char (String (ascii_of_z c1) EmptyString)) "o|") as [Ht | Ht].
        { discriminate Ht. }
        destruct (string_dec (String "."%char (String (ascii_of_z c1) EmptyString)) ".|") as [Hu | Hu].
        { inversion Hu; subst; solve_ascii_neq_17. }
        reflexivity.
      * destruct (Z.eqb_spec c1 32).
        { exfalso. apply (Hnospace c1); [left; reflexivity | assumption]. }
        simpl.
        destruct (string_dec (String (ascii_of_z c2) (String (ascii_of_z c1) EmptyString)) "o") as [Hs | Hs].
        { discriminate Hs. }
        destruct (string_dec (String (ascii_of_z c2) (String (ascii_of_z c1) EmptyString)) "o|") as [Ht | Ht].
        { inversion Ht; subst; solve_ascii_neq_17. }
        destruct (string_dec (String (ascii_of_z c2) (String (ascii_of_z c1) EmptyString)) ".|") as [Hu | Hu].
        { inversion Hu; subst; solve_ascii_neq_17. }
        reflexivity.
  - unfold token_output_z, token_state_rev_z.
    rewrite fold_left_token_long_state_5_17.
    + simpl.
      rewrite parse_note_output_nat_len_ge3_17.
      * reflexivity.
      * repeat rewrite length_app.
        repeat rewrite length_rev.
        repeat rewrite length_map.
        simpl. lia.
    + repeat rewrite length_app.
      repeat rewrite length_rev.
      simpl. lia.
    + intros x Hin.
      apply Hnospace.
      apply in_rev.
      exact Hin.
Qed.

Lemma split_music_z_aux_spec_17 : forall input current_group,
  ascii_range_z input ->
  ascii_range_z (rev current_group) ->
  no_space_z_list current_group ->
  map Z.to_nat (split_music_z_aux current_group input) =
    parse_music_impl_aux
      (SplitOnSpaces_aux
        (map ascii_of_z current_group)
        (string_of_list_z input)).
Proof.
  induction input as [| ch rest IH]; intros current_group Hinput Hcur Hnospace; simpl.
  - rewrite token_output_parse_note_17 by (exact Hcur || exact Hnospace).
    destruct current_group as [| c rest_group]; simpl; reflexivity.
  - pose proof (ascii_range_z_head ch rest Hinput) as Hch.
    pose proof (ascii_range_z_tail ch rest Hinput) as Hrest.
    destruct (Z.eqb_spec ch 32) as [Hspace | Hspace].
    + subst ch.
      rewrite ascii_of_z_32_17.
      destruct (ascii_dec " "%char " "%char) as [_ | Hneq]; [| contradiction].
      rewrite map_app.
      rewrite token_output_parse_note_17 by (exact Hcur || exact Hnospace).
      assert (Hempty_range : ascii_range_z (rev [])).
      { intros i Hi. rewrite Zlength_nil in Hi. lia. }
      assert (Hempty_nospace : no_space_z_list []).
      { intros x Hin. inversion Hin. }
      rewrite (IH [] Hrest Hempty_range Hempty_nospace).
      destruct current_group as [| c rest_group]; simpl.
      * reflexivity.
      * destruct (parse_note
          (string_of_list_ascii
            (rev (map ascii_of_z rest_group) ++ [ascii_of_z c]))) eqn:Hnote;
          unfold parse_note_output_nat; rewrite Hnote; reflexivity.
    + assert (Hascii_not_space : ascii_of_z ch <> " "%char).
      { intro H.
        apply ascii_of_z_space_iff_17 in H; [| lia].
        contradiction. }
      destruct (ascii_dec (ascii_of_z ch) " "%char) as [Hascii | Hascii].
      { contradiction. }
      rewrite IH.
      * reflexivity.
      * exact Hrest.
      * apply ascii_range_z_rev_cons; assumption.
      * intros x Hin.
        simpl in Hin.
        destruct Hin as [Hx | Hin].
        -- subst. exact Hspace.
        -- apply Hnospace. exact Hin.
Qed.

Lemma string_of_list_z_map_nat_music_output : forall input,
  ascii_range_z input ->
  problem_17_spec_z input (music_output_z input).
Proof.
  intros input Hrange.
  unfold problem_17_spec_z, problem_17_spec.
  rewrite music_output_split_music_z_aux.
  rewrite split_music_z_aux_spec_17.
  - reflexivity.
  - exact Hrange.
  - intros i Hi. rewrite Zlength_nil in Hi. lia.
  - intros ch Hin. contradiction.
Qed.
