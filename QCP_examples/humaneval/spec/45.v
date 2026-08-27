(* Given length of a side and high return area for a triangle.
>>> triangle_area(5, 3)
7.5 *)

Require Import Coq.Reals.Reals.
From SimpleC.SL Require Import SeparationLogic.

Local Open Scope R_scope.

(* The C program performs two binary32 operations: first [side * high],
   then multiplication by the exactly representable value 0.5f. *)
Definition triangle_area_fp32 (side high : fp32) : fp32 :=
  fp32_mul (fp32_mul side high) (fp32_of_real 0.5).

(* Besides the mathematical non-negativity requirement, keep every C
   floating-point intermediate finite when symexec runs in finite-VC mode. *)
Definition problem_45_pre (side high : fp32) : Prop :=
  fp32_isFinite side /\
  fp32_isFinite high /\
  fp32_ge side (fp32_of_real 0) /\
  fp32_ge high (fp32_of_real 0) /\
  fp32_isFinite (fp32_mul side high) /\
  fp32_isFinite (triangle_area_fp32 side high).

Definition problem_45_spec (side high output : fp32) : Prop :=
  fp32_eq output (triangle_area_fp32 side high).
