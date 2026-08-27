(* Given the lengths of three sides, return true when one of the three
   binary32 Pythagorean residuals is within the program's tolerance. *)

Require Import Coq.Reals.Reals.
From SimpleC.SL Require Import SeparationLogic.

Local Open Scope R_scope.

Definition square_fp32_157 (x : fp32) : fp32 :=
  fp32_mul x x.

Definition residual_fp32_157 (x y z : fp32) : fp32 :=
  fp32_sub
    (fp32_add (square_fp32_157 x) (square_fp32_157 y))
    (square_fp32_157 z).

Definition within_tolerance_fp32_157 (x : fp32) : Prop :=
  fp32_lt (fp32_neg (fp32_of_real 0.0001)) x /\
  fp32_lt x (fp32_of_real 0.0001).

Definition right_angle_fp32_157 (a b c : fp32) : Prop :=
  within_tolerance_fp32_157 (residual_fp32_157 a b c) \/
  within_tolerance_fp32_157 (residual_fp32_157 a c b) \/
  within_tolerance_fp32_157 (residual_fp32_157 b c a).

Definition problem_157_pre (a b c : fp32) : Prop :=
  fp32_isFinite a /\
  fp32_isFinite b /\
  fp32_isFinite c /\
  fp32_gt a (fp32_of_real 0) /\
  fp32_gt b (fp32_of_real 0) /\
  fp32_gt c (fp32_of_real 0) /\
  fp32_isFinite (fp32_neg (fp32_of_real 0.0001)) /\
  fp32_isFinite (fp32_of_real 0.0001) /\
  fp32_isFinite (square_fp32_157 a) /\
  fp32_isFinite (square_fp32_157 b) /\
  fp32_isFinite (square_fp32_157 c) /\
  fp32_isFinite
    (fp32_add (square_fp32_157 a) (square_fp32_157 b)) /\
  fp32_isFinite
    (fp32_add (square_fp32_157 a) (square_fp32_157 c)) /\
  fp32_isFinite
    (fp32_add (square_fp32_157 b) (square_fp32_157 c)) /\
  fp32_isFinite (residual_fp32_157 a b c) /\
  fp32_isFinite (residual_fp32_157 a c b) /\
  fp32_isFinite (residual_fp32_157 b c a).

Definition problem_157_spec (a b c : fp32) (res : Z) : Prop :=
  (res = 1%Z /\ right_angle_fp32_157 a b c) \/
  (res = 0%Z /\ ~ right_angle_fp32_157 a b c).
