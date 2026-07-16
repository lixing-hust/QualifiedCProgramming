(*def correct_bracketing(brackets: str):
""" brackets is a string of "(" and ")".
return True if every opening bracket has a corresponding closing bracket.

>>> correct_bracketing("(")
False
>>> correct_bracketing("()")
True
>>> correct_bracketing("(()())")
True
>>> correct_bracketing(")(()")
False
""" *)


Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Inductive balanced_parentheses : list ascii -> Prop :=
  | balanced_empty :
      balanced_parentheses []
  | balanced_wrap : forall inner,
      balanced_parentheses inner ->
      balanced_parentheses ("("%char :: inner ++ [")"%char])
  | balanced_concat : forall left right,
      balanced_parentheses left ->
      balanced_parentheses right ->
      balanced_parentheses (left ++ right).

(* problem_61_pre restricts the input to parenthesis characters. *)
Definition problem_61_pre (brackets : string) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) (list_ascii_of_string brackets).

(* problem_61_spec relates the result to the balanced-parentheses language. *)
Definition problem_61_spec (brackets : string) (output : bool) : Prop :=
  output = true <-> balanced_parentheses (list_ascii_of_string brackets).
