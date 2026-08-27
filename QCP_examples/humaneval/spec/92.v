(* Return true exactly when all three binary32 inputs represent integers and
   one of the three C binary32 additions compares equal to the remaining
   input. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
From SimpleC.SL Require Import SeparationLogic.

Definition fp32_is_integer_92 (x : fp32) : Prop :=
  fp32_isFinite x /\
  exists z : Z, fp32_to_R_total x = IZR z.

Definition fp32_sum_relation_92 (a b c : fp32) : Prop :=
  fp32_eq (fp32_add a b) c \/
  fp32_eq (fp32_add a c) b \/
  fp32_eq (fp32_add b c) a.

Definition problem_92_pre (a b c : fp32) : Prop :=
  fp32_isFinite a /\
  fp32_isFinite b /\
  fp32_isFinite c /\
  fp32_isFinite (fp32_add a b) /\
  fp32_isFinite (fp32_add a c) /\
  fp32_isFinite (fp32_add b c).

Definition problem_92_spec (a b c : fp32) (res : Z) : Prop :=
  let condition :=
    fp32_is_integer_92 a /\
    fp32_is_integer_92 b /\
    fp32_is_integer_92 c /\
    fp32_sum_relation_92 a b c in
  (res = 1%Z /\ condition) \/
  (res = 0%Z /\ ~ condition).
