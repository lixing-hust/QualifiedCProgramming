(* def simplify(x, n):
Your task is to implement a function that will simplify the expression
x * n. The function returns True if x * n evaluates to a whole number and False
otherwise. Both x and n, are string representation of a fraction, and have the following format,
<numerator>/<denominator> where both numerator and denominator are positive whole numbers.

You can assume that x, and n are valid fractions, and do not have zero as denominator.

simplify("1/5", "5/1") = True
simplify("1/6", "2/1") = False
simplify("7/10", "10/2") = False *)
(* 导入所需的Coq库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 将单个ASCII字符转换为数字 (0-9)，假设输入合法 *)
Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

(* list_ascii_to_nat parses a decimal character list with a left fold. *)
Definition list_ascii_to_nat (l : list ascii) : nat :=
  fold_left (fun acc c => acc * 10 + char_to_digit c) l 0.

(* is_digit_ascii recognizes decimal digit characters. *)
Definition is_digit_ascii (c : ascii) : Prop :=
  nat_of_ascii ("0"%char) <= nat_of_ascii c <= nat_of_ascii ("9"%char).

(* all_digits states that every character in the list is a decimal digit. *)
Definition all_digits (l : list ascii) : Prop :=
  Forall is_digit_ascii l.

(*
 * 规约：Parse_Fraction
 * 描述：将一个由ASCII字符组成的列表解析为一个由分子和分母组成的自然数对。
 *
 * 参数：
 *   s: 代表分数字符串的 list ascii。
 *   num: 解析出的分子（自然数）。
 *   den: 解析出的分母（自然数）。
 *)
Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    num = list_ascii_to_nat num_s /\
    den = list_ascii_to_nat den_s.

(*
 * 规约：simplify_spec
 * 描述：这是`simplify`函数的顶层规约。它规定了输入与期望的布尔输出之间的关系。
 *       此版本完全使用 list ascii。
 *
 * 参数：
 *   x: 代表第一个分数的 list ascii。
 *   n: 代表第二个分数的 list ascii。
 *   output: 函数的期望布尔输出。
 *)
(* A valid fraction has decimal digits on both sides of its slash. *)
Definition Valid_Fraction (s : string) (num den : nat) : Prop :=
  exists num_s den_s,
    list_ascii_of_string s = num_s ++ ["/"%char] ++ den_s /\
    all_digits num_s /\ all_digits den_s /\
    num = list_ascii_to_nat num_s /\
    den = list_ascii_to_nat den_s.

Definition problem_144_pre (x n : string) : Prop :=
  exists nx dx ny dy,
    Valid_Fraction x nx dx /\
    Valid_Fraction n ny dy /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

(* problem_144_spec states whether the product of two parsed fractions is integral. *)
Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\
    num_x > 0 /\ den_x > 0 /\
    num_n > 0 /\ den_n > 0 /\
    output = ((num_x * num_n) mod (den_x * den_n) =? 0).
