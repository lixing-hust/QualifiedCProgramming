Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_45_goal.
From SimpleC.EE Require Import C_45_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_45.
Local Open Scope sac.

Lemma proof_of_triangle_area_safety_wit_1 : triangle_area_safety_wit_1.
Proof.
  pre_process.
  unfold problem_45_pre in PreH1.
  entailer!.
Qed.

Lemma proof_of_triangle_area_safety_wit_2 : triangle_area_safety_wit_2.
Proof.
  pre_process.
  unfold problem_45_pre in PreH1.
  entailer!.
Qed.

Lemma proof_of_triangle_area_return_wit_1 : triangle_area_return_wit_1.
Proof.
  pre_process.
  unfold triangle_area_fp32.
  entailer!.
  apply fp32_eq_refl_finite_45.
  unfold problem_45_pre in PreH1.
  tauto.
Qed.
