(* Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> parse_nested_parens('(()()) ((())) () ((())()())')
[2, 3, 1, 3] *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* Characters used by the parenthesis language. *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(* A group is a non-empty string segment that does not itself contain spaces. *)
Definition SpaceFreeGroup (g : string) : Prop :=
  g <> "" /\ ~ In space (list_ascii_of_string g).

(* The input is exactly the single-space concatenation of its groups. *)
Definition SpaceDelimited (input : string) (groups : list string) : Prop :=
  String.concat " " groups = input /\ Forall SpaceFreeGroup groups.

(* Relational scan for the tail of a single top-level parenthesis group.
   The current depth is always positive while the tail is non-empty.  The only
   way to return to depth 0 is the final right parenthesis, so strings such as
   "()()" are not treated as one group. *)
Inductive MaxDepthGroupScan : string -> nat -> nat -> nat -> Prop :=
| mdgs_close : forall max_seen,
    MaxDepthGroupScan (String rparen "") 1 max_seen max_seen
| mdgs_lparen : forall t current_depth max_seen result,
    MaxDepthGroupScan t
      (S current_depth)
      (Nat.max max_seen (S current_depth))
      result ->
    MaxDepthGroupScan (String lparen t) current_depth max_seen result
| mdgs_rparen_nested : forall t current_depth max_seen result,
    MaxDepthGroupScan t (S current_depth) max_seen result ->
    MaxDepthGroupScan (String rparen t) (S (S current_depth)) max_seen result.

(* MaxDepth relates a parenthesis group to its maximum nesting depth. *)
Definition MaxDepth (g : string) (depth : nat) : Prop :=
  exists t,
    g = String lparen t /\
    MaxDepthGroupScan t 1 1 depth.

(* The input must be a sequence of balanced parenthesis groups separated by spaces. *)
Definition problem_6_pre (input : string) : Prop :=
  exists groups,
    SpaceDelimited input groups /\
    Forall (fun group => exists depth, MaxDepth group depth) groups.

(* The output contains exactly the maximum depth of each space-delimited group. *)
Definition problem_6_spec (input : string) (output : list nat) : Prop :=
  exists groups,
    SpaceDelimited input groups /\
    Forall2 MaxDepth groups output.
