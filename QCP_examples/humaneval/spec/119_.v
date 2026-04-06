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

(* 导入 Coq 的标准库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

Inductive check_parens_inner_rel : list ascii -> nat -> bool -> Prop :=
  | cpir_nil_zero : check_parens_inner_rel [] 0 true
  | cpir_nil_nonzero : forall n, n <> 0 -> check_parens_inner_rel [] n false
  | cpir_lparen : forall t counter result,
      check_parens_inner_rel t (S counter) result ->
      check_parens_inner_rel ("("%char :: t) counter result
  | cpir_rparen_zero : forall t counter,
      counter = 0 ->
      check_parens_inner_rel (")"%char :: t) counter false
  | cpir_rparen : forall t counter n' result,
      counter = S n' ->
      check_parens_inner_rel t n' result ->
      check_parens_inner_rel (")"%char :: t) counter result
  | cpir_other : forall c t counter result,
      c <> "("%char -> c <> ")"%char ->
      check_parens_inner_rel t counter result ->
      check_parens_inner_rel (c :: t) counter result.

Inductive is_balanced_rel : list ascii -> bool -> Prop :=
  | ibr_base : forall l result, check_parens_inner_rel l 0 result -> is_balanced_rel l result.

Inductive concat_rel : list ascii -> list ascii -> list ascii -> Prop :=
  | concr_base : forall l1 l2, concat_rel l1 l2 (l1 ++ l2).


(* 输入列表长度为 2，且每个字符仅为 '(' 或 ')' *)
Definition problem_119_pre (inputs : list string) : Prop :=
  length inputs = 2 /\ Forall (fun s =>
    let l := list_ascii_of_string s in
    Forall (fun c => c = "("%char \/ c = ")"%char) l) inputs.

Definition problem_119_spec (inputs : list string) (output : string) : Prop :=
  (exists s1 s2 s12,
     map list_ascii_of_string inputs = [s1; s2] /\
     concat_rel s1 s2 s12 /\
     is_balanced_rel s12 true /\
     output = "Yes") \/
  (exists s1 s2 s21,
     map list_ascii_of_string inputs = [s1; s2] /\
     concat_rel s2 s1 s21 /\
     is_balanced_rel s21 true /\
     output = "Yes") \/
  ((forall s1 s2, map list_ascii_of_string inputs <> [s1; s2] \/
    (forall s12, concat_rel s1 s2 s12 -> is_balanced_rel s12 false) /\
    (forall s21, concat_rel s2 s1 s21 -> is_balanced_rel s21 false)) /\
   output = "No").
