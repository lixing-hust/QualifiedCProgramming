Load "../spec/23".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_23_pre_z (input : list Z) : Prop :=
  problem_23_pre (string_of_list_z input).

Definition problem_23_spec_z (input : list Z) (output : Z) : Prop :=
  problem_23_spec (string_of_list_z input) (Z.to_nat output).

Lemma problem_23_spec_z_intro :
  forall input output,
    output = Zlength input ->
    problem_23_spec_z input output.
Proof.
  intros input output Hout.
  subst output.
  unfold problem_23_spec_z, problem_23_spec.
  apply nat_of_z_Zlength.
Qed.
