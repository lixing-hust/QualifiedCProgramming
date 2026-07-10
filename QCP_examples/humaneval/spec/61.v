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

(* bracket_step updates the optional depth for one parenthesis character. *)
Definition bracket_step (depth : option nat) (c : ascii) : option nat :=
  match depth with
  | None => None
  | Some d =>
      if Ascii.eqb c "("%char then Some (S d)
      else if Ascii.eqb c ")"%char then
        match d with
        | 0 => None
        | S d' => Some d'
        end
      else Some d
  end.

(* correct_bracketing folds over the string and accepts exactly final depth 0. *)
Definition correct_bracketing (s : string) : bool :=
  match fold_left bracket_step (list_ascii_of_string s) (Some 0) with
  | Some 0 => true
  | _ => false
  end.

(* problem_61_pre restricts the input to parenthesis characters. *)
Definition problem_61_pre (brackets : string) : Prop :=
  Forall (fun c => c = "("%char \/ c = ")"%char) (list_ascii_of_string brackets).

(* problem_61_spec states that output is the parenthesis-balance result. *)
Definition problem_61_spec (brackets : string) (output : bool) : Prop :=
  output = correct_bracketing brackets.

