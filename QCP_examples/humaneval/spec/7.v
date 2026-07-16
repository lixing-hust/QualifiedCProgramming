(*  Filter an input list of strings only for ones that contain given substring
>>> filter_by_substring([], 'a')
[]
>>> filter_by_substring(['abc', 'bacd', 'cde', 'array'], 'a')
['abc', 'bacd', 'array']
 *)

(* ∀str, In(str, output) ↔ (In(str, strings) ∧ Contains(str, s)) 
  ∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l
  *)

Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.


(* contains_substring_rel states that sub occurs contiguously inside s.
   In particular, EmptyString is a substring of every string. *)
Definition contains_substring (s sub : string) : Prop :=
  exists pre suf, s = pre ++ sub ++ suf.

(* filter_by_substring is stable filtering: matching strings are kept,
   non-matching strings are dropped, and the input order is preserved. *)
Inductive filter_by_substring : list string -> string -> list string -> Prop :=
  | fbsr_nil : forall sub,
      filter_by_substring [] sub []
  | fbsr_keep : forall h t sub output,
      contains_substring h sub ->
      filter_by_substring t sub output ->
      filter_by_substring (h :: t) sub (h :: output)
  | fbsr_drop : forall h t sub output,
      ~ contains_substring h sub ->
      filter_by_substring t sub output ->
      filter_by_substring (h :: t) sub output.

Definition problem_7_pre : Prop:= True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  filter_by_substring input sub output.
