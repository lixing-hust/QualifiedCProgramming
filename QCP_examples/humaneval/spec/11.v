(* """ Input are two strings a and b consisting only of 1s and 0s.
Perform binary XOR on these inputs and return result also as a string.
>>> string_xor('010', '110')
'100'
""" *)

(* Spec(a, b, output) :=
length(output) == length(a) ∧
∀ i ∈ [0, length(output)),
  a[i] = b[i] -> output[i] = '0' /\
  a[i]<>b[i] -> output[i] = '1' *)

Require Import List.
Require Import Ascii.
Require Import String.
Require Import Bool.
Import ListNotations.
Open Scope string_scope.

(* 定义 Spec 规约 *)
 
(* Pre: inputs have equal length and contain only '0' or '1' characters *)
Definition problem_11_pre (a b : string) : Prop :=
  String.length a = String.length b /\
  forall i,
    i < String.length a ->
      ((String.get i a = Some "0"%char) \/ (String.get i a = Some "1"%char)) /\
      ((String.get i b = Some "0"%char) \/ (String.get i b = Some "1"%char)).

(* 定义 Spec 规约 *)

Definition problem_11_spec (a b output : string) : Prop :=
  String.length a = String.length b /\
  String.length output = String.length a /\
  forall i,
    i < String.length output ->
    (String.get i a = String.get i b -> String.get i output = Some "0"%char) /\
    (String.get i a <> String.get i b -> String.get i output = Some "1"%char).