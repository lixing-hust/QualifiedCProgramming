(* def is_bored(S):
"""
You'll be given a string of words, and your task is to count the number
of boredoms. A boredom is a sentence that starts with the word "I".
Sentences are delimited by '.', '?' or '!'.

For example:
>>> is_bored("Hello world")
0
>>> is_bored("The sky is blue. The sun is shining. I love this weather")
1
""" *)

Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* is_sentence_delimiter recognizes punctuation that starts a new sentence. *)
Definition is_sentence_delimiter (c : ascii) : bool :=
  match c with
  | "."%char | "?"%char | "!"%char => true
  | _ => false
  end.

(* bored_state is (count, at_sentence_start, saw_starting_I). *)
Definition bored_state : Type := nat * bool * bool.

(* bored_step updates the boredom scan state for one character. *)
Definition bored_step (st : bored_state) (c : ascii) : bored_state :=
  let '(count, isstart, isi) := st in
  let add := if andb (Ascii.eqb c " "%char) isi then 1 else 0 in
  let isi' := if andb (Ascii.eqb c "I"%char) isstart then true else false in
  let isstart_after_char := if Ascii.eqb c " "%char then isstart else false in
  let isstart' := if is_sentence_delimiter c then true else isstart_after_char in
  (count + add, isstart', isi').

(* is_bored_impl counts sentences that start with the word I. *)
Definition is_bored_impl (S : string) : nat :=
  let '(count, _, _) := fold_left bored_step (list_ascii_of_string S) (0, true, false) in
  count.

(* problem_91_pre imposes no input constraints. *)
Definition problem_91_pre (S : string) : Prop := True.

(* problem_91_spec states that output is the boredom count. *)
Definition problem_91_spec (S : string) (output : nat) : Prop :=
  output = is_bored_impl S.
