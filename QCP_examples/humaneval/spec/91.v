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

Definition is_sentence_delimiter (c : ascii) : bool :=
  match c with
  | "."%char | "?"%char | "!"%char => true
  | _ => false
  end.

Fixpoint is_bored_aux (S : string) (isstart isi : bool) : nat :=
  match S with
  | "" => 0
  | String c rest =>
    let add := if andb (Ascii.eqb c " "%char) isi then 1 else 0 in
    let isi' := if andb (Ascii.eqb c "I"%char) isstart then true else false in
    let isstart_after_char := if Ascii.eqb c " "%char then isstart else false in
    let isstart' := if is_sentence_delimiter c then true else isstart_after_char in
    add + is_bored_aux rest isstart' isi'
  end.

Definition is_bored_impl (S : string) : nat :=
  is_bored_aux S true false.

(* 输入字符串可为任意内容，无额外约束 *)
Definition problem_91_pre (S : string) : Prop := True.

Definition problem_91_spec (S : string) (output : nat) : Prop :=
  output = is_bored_impl S.
