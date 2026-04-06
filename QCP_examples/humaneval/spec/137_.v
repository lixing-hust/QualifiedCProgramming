(* def compare_one(a, b):
"""
Create a function that takes integers, floats, or strings representing
real numbers, and returns the larger variable in its given variable type.
Return None if the values are equal.
Note: If a real number is represented as a string, the floating point might be . or ,

compare_one(1, 2.5) ➞ 2.5
compare_one(1, "2,3") ➞ "2,3"
compare_one("5,1", "6") ➞ "6"
compare_one("1", 1) ➞ None
""" *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

(* ==================== 输入类型 ==================== *)

(* 三种输入类型：整数、浮点数、字符串 *)
Inductive val :=
| VInt : Z -> val
| VFloat : R -> val
| VStr : string -> val.

(* ==================== 字符判断谓词 ==================== *)

(* 判断是否是十进制数字字符 '0'-'9' *)
Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

(* 将数字字符转换为其数值 0..9 *)
Definition digit_val (c : ascii) : nat :=
  Nat.sub (nat_of_ascii c) 48.

(* 判断是否为小数点分隔符 '.' (ASCII 46) 或 ',' (ASCII 44) *)
Definition is_sep (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (Nat.eqb n 46) (Nat.eqb n 44).

(* 判断是否为负号 '-' (ASCII 45) *)
Definition is_minus (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 45.

(* 判断是否为正号 '+' (ASCII 43) *)
Definition is_plus (c : ascii) : bool :=
  Nat.eqb (nat_of_ascii c) 43.

(* ==================== 数字解析关系 ==================== *)

(* 关系：将一串数字字符转成 nat（按十进制，使用累加器）
   digits_to_nat chars acc result 表示从 chars 解析，初始累加器为 acc，结果为 result
   例如: digits_to_nat ['1';'2';'3'] 0 123 *)
Inductive digits_to_nat : list ascii -> nat -> nat -> Prop :=
| dtn_nil : forall acc,
    digits_to_nat [] acc acc
| dtn_cons : forall c tl acc result,
    is_digit c = true ->
    digits_to_nat tl (acc * 10 + digit_val c) result ->
    digits_to_nat (c :: tl) acc result.

(* ==================== 字符串分割关系 ==================== *)

(* 关系：在首个分隔符处分割字符列表为整数部分和小数部分
   split_on_sep chars int_part frac_part
   例如: split_on_sep ['1';'2';'.';'3';'4'] ['1';'2'] ['3';'4']
         split_on_sep ['1';'2';'3'] ['1';'2';'3'] [] *)
Inductive split_on_sep : list ascii -> list ascii -> list ascii -> Prop :=
| sos_nil :
    split_on_sep [] [] []
| sos_sep : forall c tl,
    is_sep c = true ->
    split_on_sep (c :: tl) [] tl
| sos_cons : forall c tl int_part frac_part,
    is_sep c = false ->
    split_on_sep tl int_part frac_part ->
    split_on_sep (c :: tl) (c :: int_part) frac_part.

(* ==================== 10 的幂次关系 ==================== *)

(* 关系：10^n = r *)
Inductive pow10 : nat -> R -> Prop :=
| pow10_O :
    pow10 0%nat 1%R
| pow10_S : forall n p,
    pow10 n p ->
    pow10 (S n) (10 * p)%R.

(* ==================== 字符串解析关系 ==================== *)

(* 关系：解析字符串为 (neg, int_v, frac_v, frac_len)
   parse_string s neg int_v frac_v frac_len 表示：
   - neg: 是否为负数
   - int_v: 整数部分的值
   - frac_v: 小数部分的值（作为整数）
   - frac_len: 小数部分的位数
   
   例如: parse_string "-12.34" true 12 34 2
         parse_string "5,6" false 5 6 1
         parse_string "123" false 123 0 0 *)
Inductive parse_string : string -> bool -> nat -> nat -> nat -> Prop :=
| ps_neg_with_frac : forall s c rest int_chars frac_chars int_v frac_v,
    (* 负号，有小数部分: "-12.34" *)
    list_ascii_of_string s = c :: rest ->
    is_minus c = true ->
    split_on_sep rest int_chars frac_chars ->
    int_chars <> [] ->
    frac_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    digits_to_nat frac_chars 0 frac_v ->
    parse_string s true int_v frac_v (length frac_chars)
| ps_neg_no_frac : forall s c rest int_chars int_v,
    (* 负号，无小数部分: "-123" *)
    list_ascii_of_string s = c :: rest ->
    is_minus c = true ->
    split_on_sep rest int_chars [] ->
    int_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    parse_string s true int_v 0 0
| ps_pos_with_frac : forall s c rest int_chars frac_chars int_v frac_v,
    (* 正号，有小数部分: "+12.34" *)
    list_ascii_of_string s = c :: rest ->
    is_plus c = true ->
    split_on_sep rest int_chars frac_chars ->
    int_chars <> [] ->
    frac_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    digits_to_nat frac_chars 0 frac_v ->
    parse_string s false int_v frac_v (length frac_chars)
| ps_pos_no_frac : forall s c rest int_chars int_v,
    (* 正号，无小数部分: "+123" *)
    list_ascii_of_string s = c :: rest ->
    is_plus c = true ->
    split_on_sep rest int_chars [] ->
    int_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    parse_string s false int_v 0 0
| ps_no_sign_with_frac : forall s chars int_chars frac_chars int_v frac_v c,
    (* 无符号，有小数部分: "12.34" *)
    list_ascii_of_string s = chars ->
    chars = c :: _ ->
    is_minus c = false ->
    is_plus c = false ->
    split_on_sep chars int_chars frac_chars ->
    int_chars <> [] ->
    frac_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    digits_to_nat frac_chars 0 frac_v ->
    parse_string s false int_v frac_v (length frac_chars)
| ps_no_sign_no_frac : forall s chars int_chars int_v c,
    (* 无符号，无小数部分: "123" *)
    list_ascii_of_string s = chars ->
    chars = c :: _ ->
    is_minus c = false ->
    is_plus c = false ->
    split_on_sep chars int_chars [] ->
    int_chars <> [] ->
    digits_to_nat int_chars 0 int_v ->
    parse_string s false int_v 0 0.

(* ==================== 字符串表示实数关系 ==================== *)

(* 关系：字符串 s 表示实数 r
   str_represents s r 表示字符串 s 可以解析为实数 r
   
   计算方式: r = (如果neg则取负) (int_v + frac_v / 10^frac_len)
   例如: str_represents "2,3" 2.3
         str_represents "-5.25" (-5.25) *)
Inductive str_represents : string -> R -> Prop :=
| sr_positive : forall s int_v frac_v frac_len p,
    parse_string s false int_v frac_v frac_len ->
    pow10 frac_len p ->
    str_represents s (INR int_v + (if (frac_len =? 0)%nat then 0 else INR frac_v / p))%R
| sr_negative : forall s int_v frac_v frac_len p,
    parse_string s true int_v frac_v frac_len ->
    pow10 frac_len p ->
    str_represents s (- (INR int_v + (if (frac_len =? 0)%nat then 0 else INR frac_v / p)))%R.

(* ==================== 值转换关系 ==================== *)

(* 关系：val 类型的值对应的实数
   value_of v r 表示值 v 对应实数 r *)
Inductive value_of : val -> R -> Prop :=
| vo_int : forall z,
    value_of (VInt z) (IZR z)
| vo_float : forall r,
    value_of (VFloat r) r
| vo_str : forall s r,
    str_represents s r ->
    value_of (VStr s) r.

(* ==================== 实数比较关系 ==================== *)

(* 关系：实数比较结果
   Rcompare x y cmp 表示 x 与 y 的比较结果为 cmp *)
Inductive Rcompare : R -> R -> comparison -> Prop :=
| Rcmp_lt : forall x y,
    (x < y)%R ->
    Rcompare x y Lt
| Rcmp_eq : forall x y,
    (x = y)%R ->
    Rcompare x y Eq
| Rcmp_gt : forall x y,
    (x > y)%R ->
    Rcompare x y Gt.

(* ==================== 主规范 ==================== *)

(* 前置条件：任意 val 输入均可 *)
Definition problem_137_pre (a b : val) : Prop := True.

(* 规范：compare_one 的行为
   problem_137_spec a b res 表示：
   - 如果 a < b（作为实数），返回 Some b（较大者，保持原类型）
   - 如果 a > b（作为实数），返回 Some a（较大者，保持原类型）
   - 如果 a = b（作为实数），返回 None
   
   示例:
   compare_one(1, 2.5) ➞ 2.5        -- 1 < 2.5，返回较大者 2.5
   compare_one(1, "2,3") ➞ "2,3"    -- 1 < 2.3，返回较大者 "2,3"
   compare_one("5,1", "6") ➞ "6"    -- 5.1 < 6，返回较大者 "6"
   compare_one("1", 1) ➞ None       -- 1 = 1，相等返回 None *)
Inductive problem_137_spec : val -> val -> option val -> Prop :=
| spec_a_lt_b : forall a b ra rb,
    (* a < b：返回 b *)
    value_of a ra ->
    value_of b rb ->
    Rcompare ra rb Lt ->
    problem_137_spec a b (Some b)
| spec_a_gt_b : forall a b ra rb,
    (* a > b：返回 a *)
    value_of a ra ->
    value_of b rb ->
    Rcompare ra rb Gt ->
    problem_137_spec a b (Some a)
| spec_a_eq_b : forall a b ra rb,
    (* a = b：返回 None *)
    value_of a ra ->
    value_of b rb ->
    Rcompare ra rb Eq ->
    problem_137_spec a b None.