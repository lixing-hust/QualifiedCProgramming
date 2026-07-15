Load "../spec/86".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.

Definition ascii_of_z_86 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_86 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_86 c) (string_of_list_z_86 rest)
  end.

Definition problem_86_pre_z (s : list Z) : Prop :=
  problem_86_pre (string_of_list_z_86 s).

Definition problem_86_spec_z (s out : list Z) : Prop :=
  problem_86_spec (string_of_list_z_86 s) (string_of_list_z_86 out).

Definition ascii_le_z_86 (a b : Z) : Prop := a <= b.

Definition sorted_z_86 (l : list Z) : Prop :=
  StronglySorted ascii_le_z_86 l.

Definition sort_char_array_spec_86 (l sorted_l : list Z) : Prop :=
  Permutation l sorted_l /\
  sorted_z_86 sorted_l.

Definition emit_field_86 (first : Z) (out_l sorted_l : list Z) : list Z :=
  if Z.eqb first 0 then out_l ++ [32] ++ sorted_l else out_l ++ sorted_l.

Definition anti_shuffle_nonspace_step_86
    (s : list Z) (i first : Z) (out_l cur_l : list Z) (ch : Z) : Prop :=
  exists prev_cur_l,
    cur_l = List.app prev_cur_l [ch] /\
    0 <= i < string_length s /\
    ch = Znth i (c_string s) 0 /\
    ch <> 32 /\
    string_lib.all_ascii prev_cur_l /\
    string_lib.all_ascii cur_l /\
    Zlength cur_l = Zlength prev_cur_l + 1.

Definition anti_shuffle_commit_step_86
    (s : list Z) (i first : Z) (out_l cur_l out_next_l : list Z) : Prop :=
  0 <= i <= string_length s /\
  (i = string_length s \/ Znth i (c_string s) 0 = 32) /\
  exists sorted_l,
    sort_char_array_spec_86 cur_l sorted_l /\
    out_next_l = emit_field_86 first out_l sorted_l /\
    string_lib.all_ascii sorted_l /\
    Zlength out_next_l <= string_length s.

Definition anti_shuffle_commit_index_86 (s : list Z) (i : Z) : Prop :=
  0 <= i <= string_length s /\
  (i = string_length s \/ Znth i (c_string s) 0 = 32).

Definition copy_prefix_86
    (out_sep_l sorted_l : list Z) (copy : Z) (out_copy_l : list Z) : Prop :=
  0 <= copy <= Zlength sorted_l /\
  out_copy_l = List.app out_sep_l (sublist 0 copy sorted_l).

Definition out_sep_relation_86 (first : Z) (out_l out_sep_l : list Z) : Prop :=
  (first = 0 /\ out_sep_l = List.app out_l (32 :: nil)) \/
  (first = 1 /\ out_sep_l = out_l).

Lemma copy_prefix_zero_86 :
  forall out_sep_l sorted_l,
    copy_prefix_86 out_sep_l sorted_l 0 out_sep_l.
Proof.
  intros.
  unfold copy_prefix_86.
  split.
  - pose proof Zlength_nonneg sorted_l; lia.
  - rewrite Zsublist_nil by lia.
    rewrite app_nil_r.
    reflexivity.
Qed.

Lemma copy_prefix_snoc_86 :
  forall out_sep_l sorted_l copy out_copy_l,
    copy_prefix_86 out_sep_l sorted_l copy out_copy_l ->
    0 <= copy < Zlength sorted_l ->
    copy_prefix_86 out_sep_l sorted_l (copy + 1)
      (out_copy_l ++ Znth copy sorted_l 0 :: nil).
Proof.
  intros ? ? ? ? [Hcopy Hout] Hrange.
  unfold copy_prefix_86.
  split; [lia|].
  subst out_copy_l.
  rewrite (helper_sublist_snoc_Z sorted_l copy 0) by lia.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma copy_prefix_snoc_signed_86 :
  forall out_sep_l sorted_l copy out_copy_l,
    all_ascii sorted_l ->
    copy_prefix_86 out_sep_l sorted_l copy out_copy_l ->
    0 <= copy < Zlength sorted_l ->
    copy_prefix_86 out_sep_l sorted_l (copy + 1)
      (out_copy_l ++ signed_last_nbits (Znth copy sorted_l 0) 8 :: nil).
Proof.
  intros.
  replace (signed_last_nbits (Znth copy sorted_l 0) 8)
    with (Znth copy sorted_l 0).
  - apply copy_prefix_snoc_86; auto.
  - symmetry. apply signed_last_nbits_eq.
    + lia.
    + pose proof (H copy H1); lia.
Qed.

Lemma copy_prefix_full_86 :
  forall out_sep_l sorted_l copy out_copy_l,
    copy_prefix_86 out_sep_l sorted_l copy out_copy_l ->
    copy = Zlength sorted_l ->
    out_copy_l = List.app out_sep_l sorted_l.
Proof.
  intros ? ? ? ? [_ Hout] Hcopy.
  subst out_copy_l copy.
  replace (sublist 0 (Zlength sorted_l) sorted_l) with sorted_l; [reflexivity|].
  replace (sublist 0 (Zlength sorted_l) sorted_l)
    with (sublist 0 (Zlength sorted_l) (List.app sorted_l nil)).
  - rewrite sublist_app_exact1. reflexivity.
  - rewrite app_nil_r. reflexivity.
Qed.

Definition anti_shuffle_scan_state_86
    (s : list Z) (i first : Z) (out_l cur_l : list Z) : Prop :=
  0 <= i <= string_length s + 1 /\
  (first = 0 \/ first = 1) /\
  0 <= Zlength out_l <= string_length s /\
  Zlength out_l <= i /\
  0 <= Zlength cur_l <= string_length s /\
  Zlength cur_l <= i /\
  Zlength out_l + Zlength cur_l <= string_length s /\
  (first = 0 ->
   i <= string_length s ->
   Zlength out_l + 1 + Zlength cur_l <= string_length s) /\
  string_lib.all_ascii out_l /\
  string_lib.all_ascii cur_l.

Definition anti_shuffle_final_86 (s out_l : list Z) : Prop :=
  Zlength out_l = string_length s /\
  problem_86_spec_z s out_l.

Definition anti_shuffle_safe_86 (s : list Z) : Prop :=
  anti_shuffle_scan_state_86 s 0 1 [] [] /\
  (forall i first out_l cur_l ch,
      anti_shuffle_scan_state_86 s i first out_l cur_l ->
      0 <= i < string_length s ->
      ch = Znth i (c_string s) 0 ->
      ch <> 32 ->
      anti_shuffle_nonspace_step_86 s i first out_l (cur_l ++ [ch]) ch /\
      anti_shuffle_scan_state_86 s (i + 1) first out_l (cur_l ++ [ch])) /\
  (forall i first out_l cur_l out_next_l,
      anti_shuffle_scan_state_86 s i first out_l cur_l ->
      anti_shuffle_commit_step_86 s i first out_l cur_l out_next_l ->
      anti_shuffle_scan_state_86 s (i + 1) 0 out_next_l []) /\
  (forall out_l,
      anti_shuffle_scan_state_86 s (string_length s + 1) 0 out_l [] ->
      anti_shuffle_final_86 s out_l) /\
  (forall i first out_l cur_l,
      anti_shuffle_scan_state_86 s i first out_l cur_l ->
      i = string_length s + 1 ->
      first = 0 ->
      cur_l = [] /\ anti_shuffle_final_86 s out_l) /\
  (forall i out_l cur_l,
      anti_shuffle_scan_state_86 s i 1 out_l cur_l ->
      i = string_length s + 1 ->
      False).

Lemma anti_shuffle_initial_86 : forall s,
  anti_shuffle_safe_86 s ->
  anti_shuffle_scan_state_86 s 0 1 [] [].
Proof.
  intros s Hsafe.
  unfold anti_shuffle_safe_86 in Hsafe.
  tauto.
Qed.

Lemma anti_shuffle_nonspace_intro_86 : forall s i first out_l cur_l ch,
  anti_shuffle_safe_86 s ->
  anti_shuffle_scan_state_86 s i first out_l cur_l ->
  0 <= i < string_length s ->
  ch = Znth i (c_string s) 0 ->
  ch <> 32 ->
  anti_shuffle_nonspace_step_86 s i first out_l (cur_l ++ [ch]) ch /\
  anti_shuffle_scan_state_86 s (i + 1) first out_l (cur_l ++ [ch]).
Proof.
  intros s i first out_l cur_l ch Hsafe Hstate Hi Hch Hneq.
  unfold anti_shuffle_safe_86 in Hsafe.
  destruct Hsafe as [_ [Hstep _]].
  eauto.
Qed.

Lemma anti_shuffle_commit_intro_86 : forall s i first out_l cur_l out_next_l,
  anti_shuffle_safe_86 s ->
  anti_shuffle_scan_state_86 s i first out_l cur_l ->
  anti_shuffle_commit_step_86 s i first out_l cur_l out_next_l ->
  anti_shuffle_scan_state_86 s (i + 1) 0 out_next_l [].
Proof.
  intros s i first out_l cur_l out_next_l Hsafe Hstate Hcommit.
  unfold anti_shuffle_safe_86 in Hsafe.
  destruct Hsafe as [_ [_ [Hstep _]]].
  eauto.
Qed.

Lemma anti_shuffle_final_intro_86 : forall s out_l,
  anti_shuffle_safe_86 s ->
  anti_shuffle_scan_state_86 s (string_length s + 1) 0 out_l [] ->
  anti_shuffle_final_86 s out_l.
Proof.
  intros s out_l Hsafe Hstate.
  unfold anti_shuffle_safe_86 in Hsafe.
  destruct Hsafe as [_ [_ [_ [Hfinal _]]]].
  eauto.
Qed.

Lemma anti_shuffle_terminal_first1_absurd_86 : forall s i out_l cur_l,
  anti_shuffle_safe_86 s ->
  anti_shuffle_scan_state_86 s i 1 out_l cur_l ->
  i = string_length s + 1 ->
  False.
Proof.
  intros s i out_l cur_l Hsafe Hstate Hi.
  unfold anti_shuffle_safe_86 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ Habsurd]]]]].
  eauto.
Qed.

Lemma sort_char_array_spec_len0_86 : forall l,
  Zlength l = 0 ->
  sort_char_array_spec_86 l l.
Proof.
  intros l Hlen.
  assert (l = []).
  { apply Zlength_nil_inv. exact Hlen. }
  subst.
  split.
  - reflexivity.
  - constructor.
Qed.

Lemma sort_char_array_spec_len1_86 : forall l,
  Zlength l = 1 ->
  sort_char_array_spec_86 l l.
Proof.
  intros l Hlen.
  destruct l as [|x rest].
  - rewrite Zlength_nil in Hlen. lia.
  - destruct rest as [|y rest].
    + split.
      * reflexivity.
      * constructor.
        -- constructor.
        -- constructor.
    + simpl in Hlen.
      repeat rewrite Zlength_cons in Hlen.
      pose proof (Zlength_nonneg rest).
      lia.
Qed.

Lemma all_ascii_app_single_86 : forall l c,
  string_lib.all_ascii l ->
  0 <= c <= 127 ->
  string_lib.all_ascii (l ++ [c]).
Proof.
  intros l c Hall Hc.
  unfold string_lib.all_ascii in *.
  intros i Hi.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
  destruct (Z_lt_dec i (Zlength l)).
  - rewrite app_Znth1 by lia.
    apply Hall.
    lia.
  - rewrite app_Znth2 by lia.
    replace (i - Zlength l) with 0 by lia.
    change (Znth 0 [c] 0) with c.
    lia.
Qed.
