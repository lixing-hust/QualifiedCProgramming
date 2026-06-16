Load "../spec/95".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Import string_bridge.
From SimpleC.SL Require Import Mem SeparationLogic CommonAssertion.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

Definition problem_95_pre_z (keys : list (list Z)) : Prop :=
  problem_95_pre (map (fun s => (KeyString (string_of_list_z s), EmptyString)) keys).

Definition problem_95_spec_z (keys : list (list Z)) (ret : Z) : Prop :=
  problem_95_spec
    (map (fun s => (KeyString (string_of_list_z s), EmptyString)) keys)
    (negb (Z.eqb ret 0)).

Fixpoint string_lengths_z (keys : list (list Z)) (lens : list Z) : Prop :=
  match keys, lens with
  | nil, nil => True
  | k :: keys', len :: lens' => Zlength k = len /\ string_lengths_z keys' lens'
  | _, _ => False
  end.

Fixpoint string_rows_full
  (ptrs lens : list Z) (rows : list (list Z)) : Assertion :=
  match ptrs, lens, rows with
  | nil, nil, nil => emp
  | p :: ptrs', len :: lens', row :: rows' =>
      CharArray.full p (len + 1) (row ++ [0]) **
      string_rows_full ptrs' lens' rows'
  | _, _, _ => [| False |] && emp
  end.

Definition dict_case_prefix_z
  (_ : Z) (_ : list (list Z)) (_ _ : Z) : Prop := True.
