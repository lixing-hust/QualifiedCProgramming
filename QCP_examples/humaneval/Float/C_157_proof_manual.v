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
From SimpleC.EE Require Import C_157_goal.
From SimpleC.EE Require Import C_157_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_157.
Local Open Scope sac.

Lemma proof_of_right_angle_triangle_safety_wit_1 : right_angle_triangle_safety_wit_1.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_2 : right_angle_triangle_safety_wit_2.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_3 : right_angle_triangle_safety_wit_3.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_4 : right_angle_triangle_safety_wit_4.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_5 : right_angle_triangle_safety_wit_5.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_6 : right_angle_triangle_safety_wit_6.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_7 : right_angle_triangle_safety_wit_7.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_8 : right_angle_triangle_safety_wit_8.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_9 : right_angle_triangle_safety_wit_9.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_11 : right_angle_triangle_safety_wit_11.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_12 : right_angle_triangle_safety_wit_12.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_14 : right_angle_triangle_safety_wit_14.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_15 : right_angle_triangle_safety_wit_15.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_16 : right_angle_triangle_safety_wit_16.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_17 : right_angle_triangle_safety_wit_17.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_20 : right_angle_triangle_safety_wit_20.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_21 : right_angle_triangle_safety_wit_21.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_22 : right_angle_triangle_safety_wit_22.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_23 : right_angle_triangle_safety_wit_23.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_24 : right_angle_triangle_safety_wit_24.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_25 : right_angle_triangle_safety_wit_25.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_26 : right_angle_triangle_safety_wit_26.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_safety_wit_27 : right_angle_triangle_safety_wit_27.
Proof. pre_process. unfold problem_157_pre in *. entailer!. Qed.

Lemma proof_of_right_angle_triangle_return_wit_1 : right_angle_triangle_return_wit_1.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  right; split; [reflexivity|].
  intros [[Hlow1 Hup1]|[[Hlow2 Hup2]|[Hlow3 Hup3]]].
  all: match goal with
       | Hge : fp32_ge ?x ?y, Hlt : fp32_lt ?x ?y |- False =>
           exact ((fp32_ge_not_lt_157 x y Hge) Hlt)
       end.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_2 : right_angle_triangle_return_wit_2.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  right; split; [reflexivity|].
  intros [[Hlow1 Hup1]|[[Hlow2 Hup2]|[Hlow3 Hup3]]].
  all: match goal with
       | Hge : fp32_ge ?x ?y, Hlt : fp32_lt ?x ?y |- False =>
           exact ((fp32_ge_not_lt_157 x y Hge) Hlt)
       end.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_3 : right_angle_triangle_return_wit_3.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  right; split; [reflexivity|].
  intros [[Hlow1 Hup1]|[[Hlow2 Hup2]|[Hlow3 Hup3]]].
  all: match goal with
       | Hge : fp32_ge ?x ?y, Hlt : fp32_lt ?x ?y |- False =>
           exact ((fp32_ge_not_lt_157 x y Hge) Hlt)
       end.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_4 : right_angle_triangle_return_wit_4.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  right; split; [reflexivity|].
  intros [[Hlow1 Hup1]|[[Hlow2 Hup2]|[Hlow3 Hup3]]].
  all: match goal with
       | Hge : fp32_ge ?x ?y, Hlt : fp32_lt ?x ?y |- False =>
           exact ((fp32_ge_not_lt_157 x y Hge) Hlt)
       end.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_5 : right_angle_triangle_return_wit_5.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  right; split; [reflexivity|].
  intros [[Hlow1 Hup1]|[[Hlow2 Hup2]|[Hlow3 Hup3]]].
  all: match goal with
       | Hge : fp32_ge ?x ?y, Hlt : fp32_lt ?x ?y |- False =>
           exact ((fp32_ge_not_lt_157 x y Hge) Hlt)
       end.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_6 : right_angle_triangle_return_wit_6.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  right; split; [reflexivity|].
  intros [[Hlow1 Hup1]|[[Hlow2 Hup2]|[Hlow3 Hup3]]].
  all: match goal with
       | Hge : fp32_ge ?x ?y, Hlt : fp32_lt ?x ?y |- False =>
           exact ((fp32_ge_not_lt_157 x y Hge) Hlt)
       end.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_7 : right_angle_triangle_return_wit_7.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  right; split; [reflexivity|].
  intros [[Hlow1 Hup1]|[[Hlow2 Hup2]|[Hlow3 Hup3]]].
  all: match goal with
       | Hge : fp32_ge ?x ?y, Hlt : fp32_lt ?x ?y |- False =>
           exact ((fp32_ge_not_lt_157 x y Hge) Hlt)
       end.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_8 : right_angle_triangle_return_wit_8.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  right; split; [reflexivity|].
  intros [[Hlow1 Hup1]|[[Hlow2 Hup2]|[Hlow3 Hup3]]].
  all: match goal with
       | Hge : fp32_ge ?x ?y, Hlt : fp32_lt ?x ?y |- False =>
           exact ((fp32_ge_not_lt_157 x y Hge) Hlt)
       end.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_9 : right_angle_triangle_return_wit_9.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  left; split; [reflexivity|].
  right; right; split; assumption.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_10 : right_angle_triangle_return_wit_10.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  left; split; [reflexivity|].
  right; right; split; assumption.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_11 : right_angle_triangle_return_wit_11.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  left; split; [reflexivity|].
  right; right; split; assumption.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_12 : right_angle_triangle_return_wit_12.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  left; split; [reflexivity|].
  right; right; split; assumption.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_13 : right_angle_triangle_return_wit_13.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  left; split; [reflexivity|].
  right; left; split; assumption.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_14 : right_angle_triangle_return_wit_14.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
  left; split; [reflexivity|].
  right; left; split; assumption.
Qed.

Lemma proof_of_right_angle_triangle_return_wit_15 : right_angle_triangle_return_wit_15.
Proof.
  pre_process.
  unfold problem_157_spec, right_angle_fp32_157,
    within_tolerance_fp32_157, residual_fp32_157, square_fp32_157.
  entailer!.
Qed.
