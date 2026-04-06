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

(* 辅助关系：将list ascii转换为自然数 *)
Inductive list_ascii_to_nat_rel : list ascii -> nat -> Prop :=
| latn_nil : list_ascii_to_nat_rel [] 0
| latn_cons : forall c l n,
    list_ascii_to_nat_rel l n ->
    list_ascii_to_nat_rel (l ++ [c]) (n * 10 + char_to_digit c).

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
    list_ascii_to_nat_rel num_s num /\
    list_ascii_to_nat_rel den_s den.

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
 (* 约束：x 与 n 均为有效分数串，且分子/分母为正整数 *)
Definition problem_144_pre (x n : string) : Prop :=
  exists nx dx ny dy,
    Parse_Fraction (list_ascii_of_string x) nx dx /\
    Parse_Fraction (list_ascii_of_string n) ny dy /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    (* 1. 解析输入的 list ascii *)
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\

    (* 2. 根据题目描述，分子和分母都是正整数（在nat中即 > 0） *)
    num_x > 0 /\ den_x > 0 /\
    num_n > 0 /\ den_n > 0 /\

    (* 3. 定义核心逻辑：乘积是否为整数 *)
    let product_num := num_x * num_n in
    let product_den := den_x * den_n in
    output = if (product_num mod product_den) =? 0
             then true
             else false.