(* You are given a list of two strings, both strings consist of open
parentheses '(' or close parentheses ')' only.
Your job is to check if it is possible to concatenate the two strings in
some order, that the resulting string will be good.
A string S is considered to be good if and only if all parentheses in S
are balanced. For example: the string '(())()' is good, while the string
'())' is not.
Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.

Examples:
match_parens(['()(', ')']) == 'Yes'
match_parens([')', ')']) == 'No' *)

(* 导入 Coq 的标准库 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* paren_step updates the optional balance depth for one parenthesis character. *)
Definition paren_step (counter : option nat) (c : ascii) : option nat :=
  match counter with
  | None => None
  | Some n =>
      if Ascii.eqb c "("%char then Some (S n)
      else if Ascii.eqb c ")"%char then
        match n with
        | 0 => None
        | S n' => Some n'
        end
      else Some n
  end.

(*
  is_balanced 函数
  修正：现在直接接收一个 list ascii 作为输入。
*)
Definition is_balanced (l : list ascii) : bool :=
  match fold_left paren_step l (Some 0) with
  | Some 0 => true
  | _ => false
  end.

(* match_parens_impl checks both concatenation orders of the two input rows. *)
Definition match_parens_impl (inputs : list (list ascii)) : string :=
  match inputs with
  | [s1; s2] =>
    (* "++" 现在是列表拼接操作符 *)
    if orb (is_balanced (s1 ++ s2)) (is_balanced (s2 ++ s1))
    then "Yes"%string
    else "No"%string
  | _ => "No"%string (* 处理非预期输入，例如列表长度不为2 *)
  end.

(* match_parens converts string inputs to character lists before checking. *)
Definition match_parens (inputs : list string) : string :=
  match_parens_impl (map list_ascii_of_string inputs).

(* problem_119_pre requires exactly two parenthesis-only strings. *)
Definition problem_119_pre (inputs : list string) : Prop :=
  length inputs = 2 /\ Forall (fun s =>
    let l := list_ascii_of_string s in
    Forall (fun c => c = "("%char \/ c = ")"%char) l) inputs.

(* problem_119_spec states that output is Yes exactly when one concatenation is balanced. *)
Definition problem_119_spec (inputs : list string) (output : string) : Prop :=
  output = match_parens inputs.
