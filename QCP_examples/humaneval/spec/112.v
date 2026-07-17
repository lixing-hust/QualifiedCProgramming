(* Task
We are given two strings s and c, you have to deleted all the characters in s that are equal to any character in c
then check if the result string is palindrome.
A string is called palindrome if it reads the same backward as forward.
You should return a tuple containing the result string and True/False for the check.
Example
For s = "abcde", c = "ae", the result should be ('bcd',False)
For s = "abcdef", c = "b" the result should be ('acdef',False)
For s = "abcdedcba", c = "ab", the result should be ('cdedc',True)
*)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.

(* The indices occur in the same order as their characters in the source. *)
Definition strictly_increasing (indices : list nat) : Prop :=
  Forall
    (fun adjacent => (fst adjacent < snd adjacent)%nat)
    (combine indices (tl indices)).

(* [result] contains exactly the source characters whose indices are not
   occupied by a character from [removed], in their original order. *)
Definition delete_chars_rel
    (source removed result : list ascii) : Prop :=
  exists indices,
    strictly_increasing indices /\
    Forall2
      (fun index ch =>
         nth_error source index = Some ch /\ ~ In ch removed)
      indices result /\
    (forall index ch,
       nth_error source index = Some ch ->
       (In index indices <-> ~ In ch removed)).

(* The flag is true exactly when the remaining character sequence is a
   palindrome. *)
Definition palindrome_flag (result : list ascii) (flag : bool) : Prop :=
  flag = true <-> result = rev result.

(* problem_112_pre restricts both strings to lowercase letters. *)
Definition problem_112_pre (s c : string) : Prop :=
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) ls /\
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) lc.

(* The output string and flag are related directly to the two input strings. *)
Definition problem_112_spec (s c : string) (output : string * bool) : Prop :=
  let source := list_ascii_of_string s in
  let removed := list_ascii_of_string c in
  let result := list_ascii_of_string (fst output) in
  delete_chars_rel source removed result /\
  palindrome_flag result (snd output).
