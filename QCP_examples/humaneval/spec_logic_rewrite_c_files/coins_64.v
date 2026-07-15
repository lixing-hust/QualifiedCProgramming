Load "../spec/64".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Parameter LitMap : string -> addr.

Definition ascii_of_z_64 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_64 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_64 c) (string_of_list_z_64 rest)
  end.

Definition problem_64_pre_z (s : list Z) : Prop :=
  problem_64_pre (string_of_list_z_64 s).

Definition problem_64_spec_z (s : list Z) (output : Z) : Prop :=
  problem_64_spec (string_of_list_z_64 s) (Z.to_nat output).

Definition vowel_literal_64 : string := "aeiouAEIOU"%string.

Definition all_vowel_literals_64 : list string :=
  [vowel_literal_64].

Definition vowel_payload_64 : list Z :=
  [97; 101; 105; 111; 117; 65; 69; 73; 79; 85].

Definition vowel_ptr_64 (LM : string -> Z) : Z :=
  LM vowel_literal_64.

Definition vowel_payload_safe_64 : Prop :=
  string_lib.valid_string vowel_payload_64 /\
  all_ascii vowel_payload_64 /\
  string_length vowel_payload_64 < INT_MAX.

Definition vowel_literal_heap_64 (LM : string -> Z) : Assertion :=
  string_lib.store_string (vowel_ptr_64 LM) vowel_payload_64 **
  GlobalStrings_missing LM all_vowel_literals_64.

Definition regular_vowel_code_64 (c : Z) : Prop :=
  c = 97 \/ c = 101 \/ c = 105 \/ c = 111 \/ c = 117 \/
  c = 65 \/ c = 69 \/ c = 73 \/ c = 79 \/ c = 85.

Definition y_code_64 (c : Z) : Prop :=
  c = 121 \/ c = 89.

Definition vowel_count_state_64 (s : list Z) (i count : Z) : Prop :=
  0 <= i <= string_length s /\ 0 <= count <= i.

Definition vowel_regular_step_64 (s : list Z) (i count : Z) : Prop :=
  0 <= i < string_length s /\
  regular_vowel_code_64 (Znth i (c_string s) 0) /\
  vowel_count_state_64 s (i + 1) count.

Definition vowel_miss_step_64 (s : list Z) (i count : Z) : Prop :=
  0 <= i < string_length s /\
  ~ regular_vowel_code_64 (Znth i (c_string s) 0) /\
  vowel_count_state_64 s (i + 1) count.

Definition vowel_final_empty_64 (s : list Z) (count : Z) : Prop :=
  string_length s = 0 /\ count = 0 /\ problem_64_spec_z s count.

Definition vowel_final_y_64 (s : list Z) (count : Z) : Prop :=
  0 < string_length s /\
  y_code_64 (Znth (string_length s - 1) (c_string s) 0) /\
  problem_64_spec_z s count.

Definition vowel_final_not_y_64 (s : list Z) (count : Z) : Prop :=
  0 < string_length s /\
  ~ y_code_64 (Znth (string_length s - 1) (c_string s) 0) /\
  problem_64_spec_z s count.

Definition vowel_count_safe_64 (s : list Z) : Prop :=
  vowel_count_state_64 s 0 0 /\
  (forall i count,
      vowel_count_state_64 s i count ->
      0 <= i < string_length s ->
      regular_vowel_code_64 (Znth i (c_string s) 0) ->
      vowel_regular_step_64 s i (count + 1)) /\
  (forall i count,
      vowel_count_state_64 s i count ->
      0 <= i < string_length s ->
      ~ regular_vowel_code_64 (Znth i (c_string s) 0) ->
      vowel_miss_step_64 s i count) /\
  (forall count,
      vowel_count_state_64 s (string_length s) count ->
      string_length s = 0 ->
      vowel_final_empty_64 s count) /\
  (forall count,
      vowel_count_state_64 s (string_length s) (count - 1) ->
      0 < string_length s ->
      y_code_64 (Znth (string_length s - 1) (c_string s) 0) ->
      vowel_final_y_64 s count) /\
  (forall count,
      vowel_count_state_64 s (string_length s) count ->
      0 < string_length s ->
      ~ y_code_64 (Znth (string_length s - 1) (c_string s) 0) ->
      vowel_final_not_y_64 s count).

Lemma vowel_count_initial_64 : forall s,
  vowel_count_safe_64 s ->
  vowel_count_state_64 s 0 0.
Proof.
  intros s Hsafe.
  unfold vowel_count_safe_64 in Hsafe.
  tauto.
Qed.

Lemma vowel_regular_step_intro_64 : forall s i count,
  vowel_count_safe_64 s ->
  vowel_count_state_64 s i (count - 1) ->
  0 <= i < string_length s ->
  regular_vowel_code_64 (Znth i (c_string s) 0) ->
  vowel_regular_step_64 s i count.
Proof.
  intros s i count Hsafe Hstate Hi Hreg.
  unfold vowel_count_safe_64 in Hsafe.
  destruct Hsafe as [_ [Hstep _]].
  replace count with ((count - 1) + 1) by lia.
  apply Hstep; assumption.
Qed.

Lemma vowel_miss_step_intro_64 : forall s i count,
  vowel_count_safe_64 s ->
  vowel_count_state_64 s i count ->
  0 <= i < string_length s ->
  ~ regular_vowel_code_64 (Znth i (c_string s) 0) ->
  vowel_miss_step_64 s i count.
Proof.
  intros s i count Hsafe Hstate Hi Hmiss.
  unfold vowel_count_safe_64 in Hsafe.
  destruct Hsafe as [_ [_ [Hstep _]]].
  apply Hstep; assumption.
Qed.

Lemma vowel_final_empty_intro_64 : forall s count,
  vowel_count_safe_64 s ->
  vowel_count_state_64 s (string_length s) count ->
  string_length s = 0 ->
  vowel_final_empty_64 s count.
Proof.
  intros s count Hsafe Hstate Hlen.
  unfold vowel_count_safe_64 in Hsafe.
  destruct Hsafe as [_ [_ [_ [Hfinal _]]]].
  apply Hfinal; assumption.
Qed.

Lemma vowel_final_y_intro_64 : forall s count,
  vowel_count_safe_64 s ->
  vowel_count_state_64 s (string_length s) (count - 1) ->
  0 < string_length s ->
  y_code_64 (Znth (string_length s - 1) (c_string s) 0) ->
  vowel_final_y_64 s count.
Proof.
  intros s count Hsafe Hstate Hpos Hy.
  unfold vowel_count_safe_64 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [Hfinal _]]]]].
  apply Hfinal; assumption.
Qed.

Lemma vowel_final_not_y_intro_64 : forall s count,
  vowel_count_safe_64 s ->
  vowel_count_state_64 s (string_length s) count ->
  0 < string_length s ->
  ~ y_code_64 (Znth (string_length s - 1) (c_string s) 0) ->
  vowel_final_not_y_64 s count.
Proof.
  intros s count Hsafe Hstate Hpos Hy.
  unfold vowel_count_safe_64 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ Hfinal]]]]].
  apply Hfinal; assumption.
Qed.

Lemma all_ascii_c_string_inside_64 : forall s i,
  all_ascii s ->
  0 <= i < string_length s ->
  0 <= Znth i (c_string s) 0 <= 127.
Proof.
  intros s i Hascii Hi.
  rewrite c_string_Znth_inside by exact Hi.
  apply Hascii.
  unfold string_length in Hi.
  exact Hi.
Qed.

Lemma Znth_In_range_64 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma c_string_nonzero_inside_64 : forall s i,
  string_lib.valid_string s ->
  0 <= i < string_length s ->
  Znth i (c_string s) 0 <> 0.
Proof.
  intros s i Hvalid Hi.
  destruct Hvalid as [_ Hno_nul].
  rewrite c_string_Znth_inside by exact Hi.
  apply Hno_nul.
  unfold string_length in Hi.
  exact Hi.
Qed.

Lemma vowel_lit_to_store_64 : forall LM,
  store_stringLit (LM vowel_literal_64) vowel_literal_64 |--
  string_lib.store_string (vowel_ptr_64 LM) vowel_payload_64.
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold vowel_ptr_64, vowel_payload_64, vowel_literal_64.
  simpl.
  entailer!.
Qed.

Lemma vowel_payload_safe_proof_64 : vowel_payload_safe_64.
Proof.
  unfold vowel_payload_safe_64, string_lib.valid_string, string_lib.all_ascii,
    string_lib.no_inner_nul, all_ascii, no_inner_nul,
    string_length, vowel_payload_64, vowel_literal_64.
  assert (Hascii :
    forall i : Z,
      0 <= i < Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] ->
      0 <= Znth i [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0 <= 127).
  {
    intros i Hi.
    change (Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85]) with 10 in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
            i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    try change (Znth 0 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 97;
    try change (Znth 1 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 101;
    try change (Znth 2 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 105;
    try change (Znth 3 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 111;
    try change (Znth 4 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 117;
    try change (Znth 5 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 65;
    try change (Znth 6 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 69;
    try change (Znth 7 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 73;
    try change (Znth 8 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 79;
    try change (Znth 9 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 85;
    lia.
  }
  assert (Hlen : Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] < 2147483647) by
    (change (Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85]) with 10; lia).
  assert (Hnonzero :
    forall i : Z,
      0 <= i < Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] ->
      Znth i [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0 <> 0).
  {
    intros i Hi.
    pose proof (Hascii i Hi).
    change (Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85]) with 10 in Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
            i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
    destruct H0 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    try change (Znth 0 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 97;
    try change (Znth 1 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 101;
    try change (Znth 2 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 105;
    try change (Znth 3 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 111;
    try change (Znth 4 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 117;
    try change (Znth 5 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 65;
    try change (Znth 6 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 69;
    try change (Znth 7 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 73;
    try change (Znth 8 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 79;
    try change (Znth 9 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 85;
    lia.
  }
  split.
  - split; [exact Hascii | exact Hnonzero].
  - split; [exact Hascii | exact Hlen].
Qed.

Lemma vowel_payload_regular_at_64 : forall i c,
  0 <= i < string_length vowel_payload_64 ->
  Znth i vowel_payload_64 0 = c ->
  regular_vowel_code_64 c.
Proof.
  intros i c Hi Hnth.
  unfold vowel_payload_64, vowel_literal_64, string_length in Hi, Hnth.
  change (Zlength [97; 101; 105; 111; 117; 65; 69; 73; 79; 85]) with 10 in Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
  try change (Znth 0 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 97 in Hnth;
  try change (Znth 1 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 101 in Hnth;
  try change (Znth 2 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 105 in Hnth;
  try change (Znth 3 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 111 in Hnth;
  try change (Znth 4 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 117 in Hnth;
  try change (Znth 5 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 65 in Hnth;
  try change (Znth 6 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 69 in Hnth;
  try change (Znth 7 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 73 in Hnth;
  try change (Znth 8 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 79 in Hnth;
  try change (Znth 9 [97; 101; 105; 111; 117; 65; 69; 73; 79; 85] 0) with 85 in Hnth;
  subst c;
  unfold regular_vowel_code_64; tauto.
Qed.

Lemma vowel_payload_contains_regular_64 : forall c ret base,
  c <> 0 ->
  strchr_result vowel_payload_64 c ret base ->
  ret <> 0 ->
  regular_vowel_code_64 c.
Proof.
  intros c ret base Hc Hres Hret.
  unfold strchr_result in Hres.
  destruct Hres as [[i [Hi [Hnth [_ [_ _]]]]] |
                    [_ [[Hcz Hret0] | [_ Hret0]]]].
  - eapply vowel_payload_regular_at_64; eauto.
  - contradiction.
  - subst ret. contradiction.
Qed.

Lemma vowel_payload_miss_not_regular_64 : forall c base,
  strchr_result vowel_payload_64 c 0 base ->
  ~ regular_vowel_code_64 c.
Proof.
  intros c base Hres Hreg.
  unfold strchr_result in Hres.
  destruct Hres as [[i [_ [_ [_ [_ Hnz]]]]] |
                    [Hnone _]].
  - contradiction.
  - unfold regular_vowel_code_64 in Hreg.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    end; subst c;
    match goal with
    | |- False =>
        lazymatch goal with
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 97 |- _ =>
            specialize (Hnone 0); apply Hnone;
            [cbv; split; congruence |
             change (Znth 0 vowel_payload_64 0) with 97; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 101 |- _ =>
            specialize (Hnone 1); apply Hnone;
            [cbv; split; congruence |
             change (Znth 1 vowel_payload_64 0) with 101; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 105 |- _ =>
            specialize (Hnone 2); apply Hnone;
            [cbv; split; congruence |
             change (Znth 2 vowel_payload_64 0) with 105; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 111 |- _ =>
            specialize (Hnone 3); apply Hnone;
            [cbv; split; congruence |
             change (Znth 3 vowel_payload_64 0) with 111; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 117 |- _ =>
            specialize (Hnone 4); apply Hnone;
            [cbv; split; congruence |
             change (Znth 4 vowel_payload_64 0) with 117; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 65 |- _ =>
            specialize (Hnone 5); apply Hnone;
            [cbv; split; congruence |
             change (Znth 5 vowel_payload_64 0) with 65; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 69 |- _ =>
            specialize (Hnone 6); apply Hnone;
            [cbv; split; congruence |
             change (Znth 6 vowel_payload_64 0) with 69; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 73 |- _ =>
            specialize (Hnone 7); apply Hnone;
            [cbv; split; congruence |
             change (Znth 7 vowel_payload_64 0) with 73; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 79 |- _ =>
            specialize (Hnone 8); apply Hnone;
            [cbv; split; congruence |
             change (Znth 8 vowel_payload_64 0) with 79; reflexivity]
        | Hnone : forall k, _ -> Znth k vowel_payload_64 0 <> 85 |- _ =>
            specialize (Hnone 9); apply Hnone;
            [cbv; split; congruence |
             change (Znth 9 vowel_payload_64 0) with 85; reflexivity]
        end
    end.
Qed.
