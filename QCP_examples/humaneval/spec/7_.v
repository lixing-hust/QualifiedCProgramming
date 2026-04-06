(*  Filter an input list of strings only for ones that contain given substring
>>> filter_by_substring([], 'a')
[]
>>> filter_by_substring(['abc', 'bacd', 'cde', 'array'], 'a')
['abc', 'bacd', 'array']
 *)

Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.

(* sub 是 s 的子串，当且仅当存在前缀 pre 与后缀 suf 使得 s = pre ++ sub ++ suf。
   约定：空串是任何字符串的子串。 *)
Inductive contains_substring_rel : string -> string -> Prop :=
  | csr_empty_any : forall s, contains_substring_rel s EmptyString
  | csr_split : forall pre sub suf, contains_substring_rel (pre ++ sub ++ suf) sub.

Inductive filter_by_substring_impl_rel : list string -> string -> list string -> Prop :=
  | fbsir_nil : forall sub, filter_by_substring_impl_rel [] sub []
  | fbsir_include : forall h t sub output,
      contains_substring_rel h sub ->
      filter_by_substring_impl_rel t sub output ->
      filter_by_substring_impl_rel (h :: t) sub (h :: output)
  | fbsir_exclude : forall h t sub output,
      ~ contains_substring_rel h sub ->
      filter_by_substring_impl_rel t sub output ->
      filter_by_substring_impl_rel (h :: t) sub output.

Definition problem_7_pre : Prop:= True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  filter_by_substring_impl_rel input sub output.
