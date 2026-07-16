(* You are given a list of two strings, both strings consist of open
parentheses '(' or close parentheses ')' only.
Your job is to check if it is possible to concatenate the two strings in
some order, that the resulting string will be good.
A string S is considered to be good if and only if all parentheses in S
are balanced. For example: the string '(())()' is good, while the string
'())' is not.
Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.

Examples:
match_parens(['()(', ')']) == 'Yes'
match_parens([')', ')']) == 'No' *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* A parenthesis sequence is balanced exactly when its total numbers of
   opening and closing parentheses agree and no prefix closes too much. *)
Definition balanced_parentheses (chars : list ascii) : Prop :=
  count_occ ascii_dec chars "("%char =
    count_occ ascii_dec chars ")"%char /\
  forall n,
    (n <= length chars)%nat ->
    count_occ ascii_dec (firstn n chars) ")"%char <=
      count_occ ascii_dec (firstn n chars) "("%char.

(* problem_119_pre requires exactly two parenthesis-only strings. *)
Definition problem_119_pre (inputs : list string) : Prop :=
  length inputs = 2 /\ Forall (fun s =>
    let l := list_ascii_of_string s in
    Forall (fun c => c = "("%char \/ c = ")"%char) l) inputs.

(* The result depends only on whether either concatenation order is balanced. *)
Definition problem_119_spec (inputs : list string) (output : string) : Prop :=
  exists s1 s2,
    inputs = [s1; s2] /\
    let chars1 := list_ascii_of_string s1 in
    let chars2 := list_ascii_of_string s2 in
    ((balanced_parentheses (chars1 ++ chars2) \/
      balanced_parentheses (chars2 ++ chars1)) /\
     output = "Yes"%string \/
     (~ balanced_parentheses (chars1 ++ chars2) /\
      ~ balanced_parentheses (chars2 ++ chars1)) /\
     output = "No"%string).
