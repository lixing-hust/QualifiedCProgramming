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

(* problem_29_pre imposes no input constraints. *)
Definition problem_29_pre (input : list string) : Prop := True.

(* Standard-library filter preserves both input order and duplicate occurrences. *)
Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  output = filter (String.prefix substring) input.
