Load "../spec/17".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_17 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_17 c) (string_of_list_z rest)
  end.

Definition string_length (s : list Z) : Z :=
  Zlength s.

Definition problem_17_pre_z (s : list Z) : Prop :=
  problem_17_pre (string_of_list_z s).

Definition problem_17_spec_z (s output : list Z) : Prop :=
  problem_17_spec (string_of_list_z s) (map Z.to_nat output).

Definition music_indices_17 (i : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat i)).

Definition music_start_17 (s : list Z) (i : Z) : bool :=
  if Z.eqb i 0 then true else Z.eqb (Znth (i - 1) (c_string s) 0) 32.

Definition music_beat_at_17 (s : list Z) (i : Z) : list Z :=
  if music_start_17 s i then
    if Z.eqb (Znth i (c_string s) 0) 111 then
      if (Z.ltb (i + 1) (Zlength s)) && (Z.eqb (Znth (i + 1) (c_string s) 0) 124)
      then [2]
      else [4]
    else if Z.eqb (Znth i (c_string s) 0) 46 then [1]
    else []
  else [].

Definition music_prefix_17 (s : list Z) (i : Z) : list Z :=
  flat_map (music_beat_at_17 s) (music_indices_17 i).

Definition music_output_17 (s : list Z) : list Z :=
  music_prefix_17 s (Zlength s).

Definition music_state_17 (s : list Z) (i : Z) (output : list Z) : Prop :=
  0 <= i <= string_length s /\
  output = music_prefix_17 s i /\
  Zlength output <= i.

Definition music_safe_input_17 (s : list Z) : Prop :=
  problem_17_spec_z s (music_output_17 s) /\
  music_state_17 s 0 [] /\
  (forall i output,
      music_state_17 s i output ->
      i < Zlength s ->
      Znth i (c_string s) 0 = 32 ->
      music_state_17 s (i + 1) output) /\
  (forall i output,
      music_state_17 s i output ->
      i + 1 < Zlength s ->
      Znth i (c_string s) 0 = 111 ->
      Znth (i + 1) (c_string s) 0 = 124 ->
      music_state_17 s (i + 2) (output ++ [2])) /\
  (forall i output,
      music_state_17 s i output ->
      i < Zlength s ->
      Znth i (c_string s) 0 = 111 ->
      (i + 1 >= Zlength s \/ Znth (i + 1) (c_string s) 0 <> 124) ->
      music_state_17 s (i + 1) (output ++ [4])) /\
  (forall i output,
      music_state_17 s i output ->
      i + 1 < Zlength s ->
      Znth i (c_string s) 0 = 46 ->
      Znth (i + 1) (c_string s) 0 = 124 ->
      music_state_17 s (i + 2) (output ++ [1])) /\
  (forall i output,
      music_state_17 s i output ->
      i < Zlength s ->
      Znth i (c_string s) 0 <> 32 ->
      Znth i (c_string s) 0 <> 111 ->
      Znth i (c_string s) 0 = 46 /\ i + 1 < Zlength s /\ Znth (i + 1) (c_string s) 0 = 124) /\
  (forall i output,
      music_state_17 s i output ->
      i >= Zlength s ->
      output = music_output_17 s).

Lemma music_safe_spec_17:
  forall s, music_safe_input_17 s -> problem_17_spec_z s (music_output_17 s).
Proof.
  intros s H; unfold music_safe_input_17 in H; tauto.
Qed.

Lemma music_safe_initial_17:
  forall s, music_safe_input_17 s -> music_state_17 s 0 [].
Proof.
  intros s H; unfold music_safe_input_17 in H; tauto.
Qed.

Lemma music_safe_space_17:
  forall s i output,
    music_safe_input_17 s ->
    music_state_17 s i output ->
    i < Zlength s ->
    Znth i (c_string s) 0 = 32 ->
    music_state_17 s (i + 1) output.
Proof.
  intros s i output Hsafe.
  unfold music_safe_input_17 in Hsafe.
  destruct Hsafe as [_ [_ [Hspace _]]].
  eauto.
Qed.

Lemma music_safe_half_17:
  forall s i output,
    music_safe_input_17 s ->
    music_state_17 s i output ->
    i + 1 < Zlength s ->
    Znth i (c_string s) 0 = 111 ->
    Znth (i + 1) (c_string s) 0 = 124 ->
    music_state_17 s (i + 2) (output ++ [2]).
Proof.
  intros s i output Hsafe.
  unfold music_safe_input_17 in Hsafe.
  destruct Hsafe as [_ [_ [_ [Hhalf _]]]].
  eauto.
Qed.

Lemma music_safe_whole_17:
  forall s i output,
    music_safe_input_17 s ->
    music_state_17 s i output ->
    i < Zlength s ->
    Znth i (c_string s) 0 = 111 ->
    (i + 1 >= Zlength s \/ Znth (i + 1) (c_string s) 0 <> 124) ->
    music_state_17 s (i + 1) (output ++ [4]).
Proof.
  intros s i output Hsafe.
  unfold music_safe_input_17 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [Hwhole _]]]]].
  eauto.
Qed.

Lemma music_safe_dot_17:
  forall s i output,
    music_safe_input_17 s ->
    music_state_17 s i output ->
    i + 1 < Zlength s ->
    Znth i (c_string s) 0 = 46 ->
    Znth (i + 1) (c_string s) 0 = 124 ->
    music_state_17 s (i + 2) (output ++ [1]).
Proof.
  intros s i output Hsafe.
  unfold music_safe_input_17 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [Hdot _]]]]]].
  eauto.
Qed.

Lemma music_safe_dot_info_17:
  forall s i output,
    music_safe_input_17 s ->
    music_state_17 s i output ->
    i < Zlength s ->
    Znth i (c_string s) 0 <> 32 ->
    Znth i (c_string s) 0 <> 111 ->
    Znth i (c_string s) 0 = 46 /\ i + 1 < Zlength s /\ Znth (i + 1) (c_string s) 0 = 124.
Proof.
  intros s i output Hsafe.
  unfold music_safe_input_17 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [Hchar _]]]]]]].
  eauto.
Qed.

Lemma music_safe_final_17:
  forall s i output,
    music_safe_input_17 s ->
    music_state_17 s i output ->
    i >= Zlength s ->
    output = music_output_17 s.
Proof.
  intros s i output Hsafe.
  unfold music_safe_input_17 in Hsafe.
  destruct Hsafe as [_ [_ [_ [_ [_ [_ [_ Hfinal]]]]]]].
  eauto.
Qed.
