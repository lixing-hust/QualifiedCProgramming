(*  Filter an input list of strings only for ones that start with a given prefix.
>>> filter_by_prefix([], 'a')
[]
>>> filter_by_prefix(['abc', 'bcd', 'cde', 'array'], 'a')
['abc', 'array'] *)

(* Spec(input : list string, substring : string, output list string) :=

​	∀s ∈ output, s  ∈ input /\
​	∀s ∈ output, prefix(substring, s) /\
​	∀s ∈ input, prefix(substring, s) → s ∈ output /\
​	∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* keeps_relative_order states that output preserves the input order of chosen elements. *)
Definition keeps_relative_order (input output : list string) : Prop :=
  forall i j s_i s_j,
    (i < j)%nat ->
    nth_error output i = Some s_i ->
    nth_error output j = Some s_j ->
    exists k l,
      (k < l)%nat /\
      nth_error input k = Some s_i /\
      nth_error input l = Some s_j.

(* problem_29_pre imposes no input constraints. *)
Definition problem_29_pre (input : list string) : Prop := True.

(* problem_29_spec characterizes stable filtering by the prefix predicate. *)
Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  keeps_relative_order input output /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).
