(* def correct_bracketing(brackets: str):
 brackets is a string of "<" and ">".
return True if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("<")
False
>>> correct_bracketing("<>")
True
>>> correct_bracketing("<<><>>")
True
>>> correct_bracketing("><<>")
False
*)
(* 引入Coq标准库，用于列表（List）和ASCII字符（Ascii）的定义 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.


(* A sequence is correctly bracketed exactly when the total numbers of opening
   and closing brackets agree and no prefix contains more closing brackets than
   opening brackets. *)
Definition correctly_bracketed (chars : list ascii) : Prop :=
  count_occ ascii_dec chars "<"%char =
    count_occ ascii_dec chars ">"%char /\
  forall prefix suffix,
    chars = (prefix ++ suffix)%list ->
    count_occ ascii_dec prefix ">"%char <=
      count_occ ascii_dec prefix "<"%char.


(* problem_56_pre restricts the input to angle-bracket characters. *)
Definition problem_56_pre (brackets : string) : Prop :=
  Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

(* The result is true exactly when the input satisfies the bracket relation. *)
Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> correctly_bracketed (list_ascii_of_string brackets).
