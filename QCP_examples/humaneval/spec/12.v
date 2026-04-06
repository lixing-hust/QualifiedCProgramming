(* """ Out of list of strings, return the longest one. Return the first one in case of multiple
strings of the same length. Return None in case the input list is empty.
>>> longest([])

>>> longest(['a', 'b', 'c'])
'a'
>>> longest(['a', 'bb', 'ccc'])
'ccc'
""" *)

(* Spec(input, output) :=
  (length(input) = 0 ∧ output = None) ∨
  (length(input) > 0 ∧
    ∃ i ∈ [0, length(input)),
      output = input[i] ∧
      ∀ j ∈ [0, length(input)), length(input[j]) ≤ length(output) ∧
      ∀ j ∈ [0, i), length(input[j]) < length(output)
  )
 *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no specific requirements for `longest` — accept any list of strings by default *)
Definition problem_12_pre (input : list string) : Prop := True.

Definition problem_12_spec (input : list string) (output : option string) : Prop :=
  (input = [] /\ output = None) \/
  (exists out i,
    output = Some out /\
    List.length input > 0 /\
    i < List.length input /\
    nth_error input i = Some out /\
    (forall j, j < List.length input -> exists s, nth_error input j = Some s -> String.length s <= String.length out) /\
    (forall j, j < i -> exists s, nth_error input j = Some s -> String.length s < String.length out)
  ).
