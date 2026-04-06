(* Checks if given string is a palindrome
>>> is_palindrome('')
True
>>> is_palindrome('aba')
True
>>> is_palindrome('aaaaa')
True
>>> is_palindrome('zbcd')
False *)

(* Spec(input : string, output : bool) :=
​ output = true ↔ ∀i ∈ [0, length(input) / 2), input[i] = input[length(input) - 1 - i] *)


Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.


(* Pre: no special constraints for `is_palindrome` *)
Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  (*
    output 为 true 当且仅当 (<->) 以下条件成立:
    对于所有自然数 i，如果 i 小于字符串长度的一半，
    那么在 i 位置的字符必须等于在 (length - 1 - i) 位置的字符。
  *)
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).