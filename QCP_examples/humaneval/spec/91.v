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

Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* The three characters that end one sentence and start the next. *)
Definition sentence_delimiter (c : ascii) : Prop :=
  c = "."%char \/ c = "?"%char \/ c = "!"%char.

(* [start] is the first position after a delimiter, or the beginning of the
   whole string. *)
Definition sentence_start (chars : list ascii) (start : nat) : Prop :=
  start = 0 \/
  exists delimiter_pos delimiter,
    start = S delimiter_pos /\
    nth_error chars delimiter_pos = Some delimiter /\
    sentence_delimiter delimiter.

(* Position [i] begins a sentence after ignoring its leading spaces. *)
Definition begins_sentence_at (chars : list ascii) (i : nat) : Prop :=
  exists start,
    sentence_start chars start /\
    start <= i /\
    forall j, start <= j < i -> nth_error chars j = Some " "%char.

(* A boredom is represented by the position of the [I] that begins it.
   Requiring a following space makes [I] an independent word, rather than
   merely the first letter of a word such as [It]. *)
Definition boredom_at (chars : list ascii) (i : nat) : Prop :=
  begins_sentence_at chars i /\
  nth_error chars i = Some "I"%char /\
  nth_error chars (S i) = Some " "%char.

Definition problem_91_pre (_ : string) : Prop := True.

(* [boredoms] contains every boredom position exactly once.  This states the
   result as a relation between the input, the selected sentence starts, and
   their count; it does not prescribe a scanning algorithm. *)
Definition problem_91_spec (S : string) (output : nat) : Prop :=
  exists boredoms : list nat,
    NoDup boredoms /\
    (forall i,
       In i boredoms <-> boredom_at (list_ascii_of_string S) i) /\
    output = length boredoms.
