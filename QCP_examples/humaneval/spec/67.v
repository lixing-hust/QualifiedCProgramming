(* def fruit_distribution(s,n):
"""
In this task, you will be given a string that represents a number of apples and oranges
that are distributed in a basket of fruit this basket contains
apples, oranges, and mango fruits. Given the string that represents the total number of
the oranges and apples and an integer that represent the total number of the fruits
in the basket return the number of the mango fruits in the basket.
for examble:
fruit_distribution("5 apples and 6 oranges", 19) ->19 - 5 - 6 = 8
fruit_distribution("0 apples and 1 oranges",3) -> 3 - 0 - 1 = 2
fruit_distribution("2 apples and 3 oranges", 100) -> 100 - 2 - 3 = 95
fruit_distribution("100 apples and 1 oranges",120) -> 120 - 100 - 1 = 19
""" *)
(* 引入Coq自带的库，用于处理整数（Z）和字符串（string） *)
Require Import ZArith Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.

(* char_to_digit converts an ASCII decimal digit to its numeric value. *)
Definition char_to_digit (c : ascii) : nat :=
  nat_of_ascii c - nat_of_ascii "0"%char.

(* string_to_nat parses a decimal string with a left fold. *)
Definition string_to_nat (s : string) : nat :=
  fold_left (fun acc c => acc * 10 + char_to_digit c) (list_ascii_of_string s) 0.

(*
  辅助规约: parse_fruit_string
  这个规约描述了从输入字符串 s 中解析出苹果和橘子数量的逻辑。
*)
Definition parse_fruit_string (s : string) (apples oranges : nat) : Prop :=
  exists s_apples s_oranges,
    apples = string_to_nat s_apples /\
    oranges = string_to_nat s_oranges /\
    s = (s_apples ++ " apples and " ++ s_oranges ++ " oranges")%string.

(* problem_67_spec subtracts parsed apples and oranges from the total fruit count. *)
Definition problem_67_spec (s : string) (n : nat) (ret : nat) : Prop :=
  exists apples oranges,
    parse_fruit_string s apples oranges /\
    ret = n - (apples + oranges).

(* problem_67_pre states the required fruit-string shape with decimal counts. *)
Definition problem_67_pre (s : string) (n : nat) : Prop :=
  exists s_apples s_oranges,
    s_apples <> EmptyString /\
    s_oranges <> EmptyString /\
    (forall c, In c (list_ascii_of_string s_apples) ->
      (48 <= nat_of_ascii c <= 57)%nat) /\
    (forall c, In c (list_ascii_of_string s_oranges) ->
      (48 <= nat_of_ascii c <= 57)%nat) /\
    s = (s_apples ++ " apples and " ++ s_oranges ++ " oranges")%string.
