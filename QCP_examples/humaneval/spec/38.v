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

Definition problem_38_spec (input output : string) : Prop :=
  (* 1. 基础约束：长度相等 *)
  String.length input = String.length output /\
  (
    (* 2. 定义常量 *)
    let n := ((String.length input / 3) * 3 - 1)%nat in
    let L := String.length input in

    (* 3. 对于所有索引 i，必须满足以下由逻辑连接词构成的断言 *)
    forall i, (i < L)%nat ->
      let out_char := get_char output i in
      (
        (* 情况一: i <= n *)
        ( (i <= n)%nat ->
          (
            (* 子情况 1: (i+1)%3 = 1 *)
            ( ((i + 1) mod 3 = 1%nat) /\ (out_char = get_char input (i + 2)) ) \/

            (* 子情况 2: (i+1)%3 = 2 或 0 *)
            ( (((i + 1) mod 3 = 2%nat) \/ ((i + 1) mod 3 = 0%nat)) /\ (out_char = get_char input (i - 1)) )
          )
        ) /\

        (* 情况二: i > n (等价于 not (i <= n)) *)
        ( (~(i <= n)%nat) ->
          (
            out_char = get_char input i
          )
        )
      )
  ).

