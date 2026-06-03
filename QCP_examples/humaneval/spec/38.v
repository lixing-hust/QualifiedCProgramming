(* def encode_cyclic(s: str):
"""
returns encoded string by cycling groups of three characters.
"""

def decode_cyclic(s: str):
"""
takes as input string encoded with encode_cyclic function. Returns decoded string.
"""
*)

(* 
  Spec(input ：string, output : string) :=

​	∃n， n = (length(input) / 3) *3 -1  /\
​		(∀i ∈ [0, length(input)),   i+1 % 3 = 0  → i ≤ n) /\
​		(∀i ∈ [0, n], i+1 % 3 = 2 → output[i] = input[i-1] /\ 
​							  i+1 % 3 = 1 → output[i] = input[i+2] /\ 
​							  i+1 % 3 =0 → output[i] = input[i-1]) /\
​		(∀i ∈ (n, length(input)), output[i] = input[i]) *)


Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Definition get_char (s : string) (n : nat) : ascii :=
  match String.get n s with
  | Some c => c
  | None => " "%char
  end.

(* Pre: no additional constraints for `encode/decode_cyclic` by default *)
Definition problem_38_pre (input : string) : Prop := True.

Definition decode_cyclic_source_index (len i : nat) : nat :=
  let full_len := ((len / 3) * 3)%nat in
  if (i <? full_len)%nat then
    if ((i + 1) mod 3 =? 1)%nat then i + 2 else i - 1
  else i.

Definition problem_38_spec (input output : string) : Prop :=
  String.length input = String.length output /\
  forall i, (i < String.length input)%nat ->
    get_char output i =
    get_char input (decode_cyclic_source_index (String.length input) i).
