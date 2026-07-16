(* def fix_spaces(text):
Given a string text, replace all spaces in it with underscores,
and if a string has more than 2 consecutive spaces,
then replace all consecutive spaces with -

fix_spaces("Example") == "Example"
fix_spaces("Example 1") == "Example_1"
fix_spaces(" Example 2") == "_Example_2"
fix_spaces(" Example   3") == "_Example-3" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition space : ascii := " ".
Definition underscore : ascii := "_".
Definition dash : ascii := "-".

(* A non-space chunk is a nonempty sequence containing no spaces. *)
Definition non_space_chunk (chunk : list ascii) : Prop :=
  chunk <> [] /\ Forall (fun c => c <> space) chunk.

(* A space chunk is a nonempty run consisting only of spaces. *)
Definition space_chunk (chunk : list ascii) : Prop :=
  exists n,
    (1 <= n)%nat /\
    chunk = repeat space n.

(* Each input chunk is related directly to its output chunk. *)
Definition fix_spaces_chunk
    (input_chunk output_chunk : list ascii) : Prop :=
  (non_space_chunk input_chunk /\ output_chunk = input_chunk) \/
  (exists n,
      (1 <= n <= 2)%nat /\
      input_chunk = repeat space n /\
      output_chunk = repeat underscore n) \/
  (exists n,
      (3 <= n)%nat /\
      input_chunk = repeat space n /\
      output_chunk = [dash]).

(* This condition makes every space chunk maximal: one space run cannot be
   represented by two adjacent chunks. *)
Definition no_adjacent_space_chunks (chunks : list (list ascii)) : Prop :=
  Forall
    (fun adjacent =>
       ~ (space_chunk (fst adjacent) /\ space_chunk (snd adjacent)))
    (combine chunks (tl chunks)).

Definition problem_140_pre (_ : string) : Prop := True.

Definition problem_140_spec (input output : string) : Prop :=
  exists input_chunks output_chunks,
    Forall2 fix_spaces_chunk input_chunks output_chunks /\
    no_adjacent_space_chunks input_chunks /\
    concat input_chunks = list_ascii_of_string input /\
    concat output_chunks = list_ascii_of_string output.
