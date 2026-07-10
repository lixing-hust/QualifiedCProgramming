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

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Bool.Bool.
Import ListNotations.


(* delete_chars_impl removes every character that appears in c. *)
Definition delete_chars_impl (s c : list ascii) : list ascii :=
  filter (fun h => negb (existsb (fun x => Ascii.eqb x h) c)) s.

(* is_pal_impl compares a character list with its reverse. *)
Definition is_pal_impl (s : list ascii) : bool :=
  if list_eq_dec Ascii.ascii_dec s (rev s) then true else false.

(* del_and_pal_impl returns the filtered characters and their palindrome flag. *)
Definition del_and_pal_impl (s c : list ascii) : list ascii * bool :=
  let r := delete_chars_impl s c in (r, is_pal_impl r).

(* reverse_delete converts strings to lists, filters, checks palindrome, and converts back. *)
Definition reverse_delete (s c : string) : string * bool :=
  let (r, b) := del_and_pal_impl (list_ascii_of_string s) (list_ascii_of_string c) in
  (string_of_list_ascii r, b).

(* problem_112_pre restricts both strings to lowercase letters. *)
Definition problem_112_pre (s c : string) : Prop :=
  let ls := list_ascii_of_string s in
  let lc := list_ascii_of_string c in
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) ls /\
  Forall (fun ch => let n := nat_of_ascii ch in 97 <= n /\ n <= 122) lc.

(* problem_112_spec states that output is the filtered string and palindrome flag. *)
Definition problem_112_spec (s c : string) (output : string * bool) : Prop :=
  output = reverse_delete s c.
