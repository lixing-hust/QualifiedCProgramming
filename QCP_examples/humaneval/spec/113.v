(* Given a list of strings, where each string consists of only digits, return a list.
Each element i of the output should be "the number of odd elements in the
string i of the input." where all the i's should be replaced by the number
of odd digits in the i'th string of the input.

>>> odd_count(['1234567'])
["the number of odd elements 4n the str4ng 4 of the 4nput."]
>>> odd_count(['3',"11111111"])
["the number of odd elements 1n the str1ng 1 of the 1nput.",
"the number of odd elements 8n the str8ng 8 of the 8nput."] *)

Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii.
Require Import Coq.NArith.NArith Coq.Numbers.DecimalString.
Import ListNotations.


Definition is_odd_digit (c : ascii) : bool :=
  match c with "1"%char|"3"%char|"5"%char|"7"%char|"9"%char => true | _ => false end.

Definition count_odd_digits (s : string) : nat :=
  List.length (List.filter is_odd_digit (list_ascii_of_string s)).

Definition nat_to_string (n : nat) : string :=
  NilZero.string_of_uint (N.to_uint (N.of_nat n)).

Definition replace_char_with_string (target : ascii) (replacement : string) (s : string) : string :=
  string_of_list_ascii
    (List.flat_map
       (fun c =>
          if Ascii.eqb c target
          then list_ascii_of_string replacement
          else [c])
       (list_ascii_of_string s)).

Definition process_string (s : string) : string :=
  let cnt := count_odd_digits s in
  let cnt_str := nat_to_string cnt in
  let templ := "the number of odd elements in the string i of the input."%string in
  replace_char_with_string "i"%char cnt_str templ.

Definition odd_count_impl (input : list string) : list string := map process_string input.

(* 每个字符串只包含数字字符 *)
Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s =>
    Forall (fun ch =>
      let n := nat_of_ascii ch in 48 <= n /\ n <= 57)
      (list_ascii_of_string s)) input.

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  output = odd_count_impl input.
