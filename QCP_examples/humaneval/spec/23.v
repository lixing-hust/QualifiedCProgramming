(* """ Return length of given string
>>> strlen('')
0
>>> strlen('abc')
3
""" *)

(* ​	Spec(input : string, output : int) :=

​		output = length(input) *)
Require Import String.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.