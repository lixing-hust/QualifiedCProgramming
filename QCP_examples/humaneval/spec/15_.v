(* """ Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> string_sequence(0)
'0'
>>> string_sequence(5)
'0 1 2 3 4 5'
""" *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.

Open Scope string_scope.

(* 将自然数转换为十进制字符串的实现 *)
Definition string_of_nat (n : nat) : string :=
  (* 对 0 做特殊处理 *)
  match n with
  | 0 => "0"
  | _ =>
    (* 生成数字的倒序 ascii 列表，然后反转并组装为 string.
     为了满足 Coq 的递归终止检查，我们使用带有 fuel 参数的辅助递归，
     对 fuel 进行结构递归（每次递归 fuel-1）。初始时传入 fuel = n，
     这对于所有 n>0 来说足够大以完成所有位的拆分。 *)
    let fix digits_rev_aux (m fuel : nat) : list ascii :=
      match fuel with
      | 0 => [] (* unreachable for adequate initial fuel; 保守返回空列表 *)
      | S fuel' =>
        if Nat.ltb m 10 then [Ascii.ascii_of_nat (48 + m)]
        else Ascii.ascii_of_nat (48 + (Nat.modulo m 10)) :: digits_rev_aux (Nat.div m 10) fuel'
      end in
    let digits := rev (digits_rev_aux n n) in
      fold_right (fun a acc => String a acc) EmptyString digits
  end.

Inductive seq_string_rel : nat -> nat -> string -> Prop :=
  | ssr_zero : forall start, seq_string_rel start 0 (string_of_nat start)
  | ssr_succ : forall start limit n' result,
      limit = S n' ->
      seq_string_rel (S start) n' result ->
      seq_string_rel start limit (string_of_nat start ++ " " ++ result).

(* Pre: no additional constraints for `string_sequence` by default *)
Definition problem_15_pre (n : nat) : Prop := True.

Definition problem_15_spec (n : nat) (output : string) : Prop :=
  seq_string_rel 0 n output.
