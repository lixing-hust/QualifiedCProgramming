(* """ Return list of all prefixes from shortest to longest of the input string
>>> all_prefixes('abc')
['a', 'ab', 'abc']
""" *)

(* Spec(input, output) :=

(length(input) = 0 ∧ output = {}) ∨
(length(input) > 0 ∧
  length(output) = length(input) ∧
  ∀ i ∈ [0, length(input)),
    length(output[i]) = i+1 ∧
    prefix(output[i], input)
) *)

Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `all_prefixes` by default *)
Definition problem_14_pre (input : string) : Prop := True.

Definition problem_14_spec (input : string)(output : list string) : Prop :=
  (String.length input = 0 /\ output = []) \/
  (String.length input > 0 /\
   List.length output = String.length input /\
   forall i, i < String.length input ->
     String.length (nth i output "0") = i + 1 /\
     prefix (nth i output "0") input = true).
