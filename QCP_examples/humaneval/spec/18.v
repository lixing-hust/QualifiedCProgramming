(* """ Find how many times a given substring can be found in the original string. Count overlaping cases.
>>> how_many_times('', 'a')
0
>>> how_many_times('aaa', 'a')
3
>>> how_many_times('aaaa', 'aa')
3
""" *)

(* match_at(i, input, substr) :=
  length(substr) > 0 ∧
  i + length(substr) ≤ length(input) ∧
  ∀ j ∈ [0, length(substr)), input[i + j] = substr[j]



Spec(input, substring, output) :=

​	(∃ index : list(nat),

​		∀ i ∈ [0, length(input)-length(substr)], match_at(i, input, substr) → i ∈ index ) ∧

​    (∀ i ∈ index, match_at(i, input, substr)) ∧

​	output = length(index) *)

Require Import List.
Import ListNotations.
Require Import Ascii.
Require Import String.
Require Import Nat.
Open Scope string_scope.



(* 表示从 input 的第 i 位开始，与 substr 完全匹配 *)
Definition match_at (i : nat) (input substr : string) : Prop :=
  String.length substr > 0 /\
  i + String.length substr <= String.length input /\
  (forall j, j < String.length substr -> String.get (i + j) input = String.get j substr).

(* Spec: output是input中substring出现的次数 *)
(* Pre: no additional constraints for `how_many_times` by default *)
Definition problem_18_pre (input substring : string) : Prop := True.

Definition problem_18_spec (input substring : string) (output : nat) : Prop :=
  exists indices : list nat,
    NoDup indices /\
    (* indices中所有位置都匹配 *)
    (forall i, In i indices -> match_at i input substring) /\
    (* 所有匹配位置都在indices中 *)
    (forall i, i + String.length substring <= String.length input ->
               match_at i input substring -> In i indices) /\
    (* output是匹配次数 *)
    output = List.length indices.
