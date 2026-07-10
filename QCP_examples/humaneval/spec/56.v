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


(* bracket_step updates the optional depth for one angle-bracket character. *)
Definition bracket_step (depth : option nat) (c : ascii) : option nat :=
  match depth with
  | None => None
  | Some d =>
      if Ascii.eqb c "<"%char then Some (S d)
      else if Ascii.eqb c ">"%char then
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


(* problem_56_pre restricts the input to angle-bracket characters. *)
Definition problem_56_pre (brackets : string) : Prop :=
  Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

(* problem_56_spec states that b is the angle-bracket balance result. *)
Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = correct_bracketing brackets.
