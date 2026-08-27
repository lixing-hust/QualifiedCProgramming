Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_157.
Local Open Scope sac.

(*----- Function right_angle_triangle -----*)

Definition right_angle_triangle_safety_wit_1 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "aa" ) )) # Float  |->_)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (a_pre) (a_pre)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "aa" ) )) # Float  |->_)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (a_pre) (a_pre)) ) ”
).

Definition right_angle_triangle_safety_wit_1_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "aa" ) )) # Float  |->_)
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (a_pre) (a_pre)) ) ”
.

Definition right_angle_triangle_safety_wit_2 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "bb" ) )) # Float  |->_)
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (b_pre) (b_pre)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "bb" ) )) # Float  |->_)
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (b_pre) (b_pre)) ) ”
).

Definition right_angle_triangle_safety_wit_2_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "bb" ) )) # Float  |->_)
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (b_pre) (b_pre)) ) ”
.

Definition right_angle_triangle_safety_wit_3 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "cc" ) )) # Float  |->_)
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (c_pre) (c_pre)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "cc" ) )) # Float  |->_)
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (c_pre) (c_pre)) ) ”
).

Definition right_angle_triangle_safety_wit_3_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "cc" ) )) # Float  |->_)
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (c_pre) (c_pre)) ) ”
.

Definition right_angle_triangle_safety_wit_4 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d1" ) )) # Float  |->_)
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d1" ) )) # Float  |->_)
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_4_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d1" ) )) # Float  |->_)
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_5 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d1" ) )) # Float  |->_)
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d1" ) )) # Float  |->_)
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_5_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d1" ) )) # Float  |->_)
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_6 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d2" ) )) # Float  |->_)
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d2" ) )) # Float  |->_)
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_6_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d2" ) )) # Float  |->_)
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_7 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d2" ) )) # Float  |->_)
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d2" ) )) # Float  |->_)
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_7_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d2" ) )) # Float  |->_)
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_8 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d3" ) )) # Float  |->_)
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d3" ) )) # Float  |->_)
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_8_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d3" ) )) # Float  |->_)
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_9 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d3" ) )) # Float  |->_)
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d3" ) )) # Float  |->_)
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_9_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "d3" ) )) # Float  |->_)
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_10 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "lower" ) )) # Float  |->_)
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ”
.

Definition right_angle_triangle_safety_wit_11 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_11_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ”
.

Definition right_angle_triangle_safety_wit_11_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_12 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH2 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH2 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
).

Definition right_angle_triangle_safety_wit_12_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH2 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_12_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH2 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
.

Definition right_angle_triangle_safety_wit_13 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_14 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH2 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH2 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_14_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH2 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ”
.

Definition right_angle_triangle_safety_wit_14_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH2 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_15 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_15_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ”
.

Definition right_angle_triangle_safety_wit_15_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_16 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
).

Definition right_angle_triangle_safety_wit_16_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_16_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
.

Definition right_angle_triangle_safety_wit_17 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
).

Definition right_angle_triangle_safety_wit_17_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_17_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
.

Definition right_angle_triangle_safety_wit_18 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_19 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_20 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_20_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ”
.

Definition right_angle_triangle_safety_wit_20_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_21 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_21_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ”
.

Definition right_angle_triangle_safety_wit_21_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_22 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_22_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ”
.

Definition right_angle_triangle_safety_wit_22_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_23 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ” 
  &&  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
).

Definition right_angle_triangle_safety_wit_23_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_neg ((fp32_of_real (0.0001)))) ) ”
.

Definition right_angle_triangle_safety_wit_23_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_24 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
).

Definition right_angle_triangle_safety_wit_24_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_24_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
.

Definition right_angle_triangle_safety_wit_25 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
).

Definition right_angle_triangle_safety_wit_25_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_25_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
.

Definition right_angle_triangle_safety_wit_26 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
).

Definition right_angle_triangle_safety_wit_26_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_26_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
.

Definition right_angle_triangle_safety_wit_27 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
).

Definition right_angle_triangle_safety_wit_27_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) ) ”
.

Definition right_angle_triangle_safety_wit_27_split_goal_2 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_of_real (0.0001)) ) ”
.

Definition right_angle_triangle_safety_wit_28 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH6 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH7 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_29 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_30 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_31 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition right_angle_triangle_safety_wit_32 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH6 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH7 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_safety_wit_33 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_safety_wit_34 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_safety_wit_35 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_safety_wit_36 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_safety_wit_37 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_safety_wit_38 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_safety_wit_39 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  ((( &( "upper" ) )) # Float  |-> (fp32_of_real (0.0001)))
  **  ((( &( "lower" ) )) # Float  |-> (fp32_neg ((fp32_of_real (0.0001)))))
  **  ((( &( "d3" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))))
  **  ((( &( "d2" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))))
  **  ((( &( "d1" ) )) # Float  |-> (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))))
  **  ((( &( "cc" ) )) # Float  |-> (fp32_mul (c_pre) (c_pre)))
  **  ((( &( "bb" ) )) # Float  |-> (fp32_mul (b_pre) (b_pre)))
  **  ((( &( "aa" ) )) # Float  |-> (fp32_mul (a_pre) (a_pre)))
  **  ((( &( "c" ) )) # Float  |-> c_pre)
  **  ((( &( "b" ) )) # Float  |-> b_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition right_angle_triangle_return_wit_1 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH6 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH7 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH6 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH7 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_1_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH6 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH7 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_2 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_2_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_3 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_3_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_4 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_4_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_5 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_5_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_6 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_6_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH3 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_7 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_7_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_8 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 0 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_8_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH2 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 0 )
.

Definition right_angle_triangle_return_wit_9 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH6 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH7 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH6 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH7 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_9_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH6 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH7 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 1 )
.

Definition right_angle_triangle_return_wit_10 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_10_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH5 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 1 )
.

Definition right_angle_triangle_return_wit_11 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_11_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH5 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH6 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 1 )
.

Definition right_angle_triangle_return_wit_12 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_12_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (b_pre) (b_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (a_pre) (a_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH4 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 1 )
.

Definition right_angle_triangle_return_wit_13 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_13_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH4 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH5 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 1 )
.

Definition right_angle_triangle_return_wit_14 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_14_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (c_pre) (c_pre))))) ((fp32_mul (b_pre) (b_pre)))) )) (PreH3 : (fp32_ge (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH4 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 1 )
.

Definition right_angle_triangle_return_wit_15 := 
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
) \/
(
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  TT && emp 
|--
  “ (problem_157_spec a_pre b_pre c_pre 1 ) ”
  &&  emp
).

Definition right_angle_triangle_return_wit_15_split_goal_1 := 
forall (c_pre: fp32) (b_pre: fp32) (a_pre: fp32) (PreH1 : (fp32_lt (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) (fp32_of_real (0.0001)) )) (PreH2 : (fp32_lt (fp32_neg ((fp32_of_real (0.0001)))) (fp32_sub ((fp32_add ((fp32_mul (a_pre) (a_pre))) ((fp32_mul (b_pre) (b_pre))))) ((fp32_mul (c_pre) (c_pre)))) )) (PreH3 : (problem_157_pre a_pre b_pre c_pre )) ,
  (problem_157_spec a_pre b_pre c_pre 1 )
.

Module Type VC_Correct.


Axiom proof_of_right_angle_triangle_safety_wit_1 : right_angle_triangle_safety_wit_1.
Axiom proof_of_right_angle_triangle_safety_wit_2 : right_angle_triangle_safety_wit_2.
Axiom proof_of_right_angle_triangle_safety_wit_3 : right_angle_triangle_safety_wit_3.
Axiom proof_of_right_angle_triangle_safety_wit_4 : right_angle_triangle_safety_wit_4.
Axiom proof_of_right_angle_triangle_safety_wit_5 : right_angle_triangle_safety_wit_5.
Axiom proof_of_right_angle_triangle_safety_wit_6 : right_angle_triangle_safety_wit_6.
Axiom proof_of_right_angle_triangle_safety_wit_7 : right_angle_triangle_safety_wit_7.
Axiom proof_of_right_angle_triangle_safety_wit_8 : right_angle_triangle_safety_wit_8.
Axiom proof_of_right_angle_triangle_safety_wit_9 : right_angle_triangle_safety_wit_9.
Axiom proof_of_right_angle_triangle_safety_wit_10 : right_angle_triangle_safety_wit_10.
Axiom proof_of_right_angle_triangle_safety_wit_11 : right_angle_triangle_safety_wit_11.
Axiom proof_of_right_angle_triangle_safety_wit_12 : right_angle_triangle_safety_wit_12.
Axiom proof_of_right_angle_triangle_safety_wit_13 : right_angle_triangle_safety_wit_13.
Axiom proof_of_right_angle_triangle_safety_wit_14 : right_angle_triangle_safety_wit_14.
Axiom proof_of_right_angle_triangle_safety_wit_15 : right_angle_triangle_safety_wit_15.
Axiom proof_of_right_angle_triangle_safety_wit_16 : right_angle_triangle_safety_wit_16.
Axiom proof_of_right_angle_triangle_safety_wit_17 : right_angle_triangle_safety_wit_17.
Axiom proof_of_right_angle_triangle_safety_wit_18 : right_angle_triangle_safety_wit_18.
Axiom proof_of_right_angle_triangle_safety_wit_19 : right_angle_triangle_safety_wit_19.
Axiom proof_of_right_angle_triangle_safety_wit_20 : right_angle_triangle_safety_wit_20.
Axiom proof_of_right_angle_triangle_safety_wit_21 : right_angle_triangle_safety_wit_21.
Axiom proof_of_right_angle_triangle_safety_wit_22 : right_angle_triangle_safety_wit_22.
Axiom proof_of_right_angle_triangle_safety_wit_23 : right_angle_triangle_safety_wit_23.
Axiom proof_of_right_angle_triangle_safety_wit_24 : right_angle_triangle_safety_wit_24.
Axiom proof_of_right_angle_triangle_safety_wit_25 : right_angle_triangle_safety_wit_25.
Axiom proof_of_right_angle_triangle_safety_wit_26 : right_angle_triangle_safety_wit_26.
Axiom proof_of_right_angle_triangle_safety_wit_27 : right_angle_triangle_safety_wit_27.
Axiom proof_of_right_angle_triangle_safety_wit_28 : right_angle_triangle_safety_wit_28.
Axiom proof_of_right_angle_triangle_safety_wit_29 : right_angle_triangle_safety_wit_29.
Axiom proof_of_right_angle_triangle_safety_wit_30 : right_angle_triangle_safety_wit_30.
Axiom proof_of_right_angle_triangle_safety_wit_31 : right_angle_triangle_safety_wit_31.
Axiom proof_of_right_angle_triangle_safety_wit_32 : right_angle_triangle_safety_wit_32.
Axiom proof_of_right_angle_triangle_safety_wit_33 : right_angle_triangle_safety_wit_33.
Axiom proof_of_right_angle_triangle_safety_wit_34 : right_angle_triangle_safety_wit_34.
Axiom proof_of_right_angle_triangle_safety_wit_35 : right_angle_triangle_safety_wit_35.
Axiom proof_of_right_angle_triangle_safety_wit_36 : right_angle_triangle_safety_wit_36.
Axiom proof_of_right_angle_triangle_safety_wit_37 : right_angle_triangle_safety_wit_37.
Axiom proof_of_right_angle_triangle_safety_wit_38 : right_angle_triangle_safety_wit_38.
Axiom proof_of_right_angle_triangle_safety_wit_39 : right_angle_triangle_safety_wit_39.
Axiom proof_of_right_angle_triangle_return_wit_1 : right_angle_triangle_return_wit_1.
Axiom proof_of_right_angle_triangle_return_wit_2 : right_angle_triangle_return_wit_2.
Axiom proof_of_right_angle_triangle_return_wit_3 : right_angle_triangle_return_wit_3.
Axiom proof_of_right_angle_triangle_return_wit_4 : right_angle_triangle_return_wit_4.
Axiom proof_of_right_angle_triangle_return_wit_5 : right_angle_triangle_return_wit_5.
Axiom proof_of_right_angle_triangle_return_wit_6 : right_angle_triangle_return_wit_6.
Axiom proof_of_right_angle_triangle_return_wit_7 : right_angle_triangle_return_wit_7.
Axiom proof_of_right_angle_triangle_return_wit_8 : right_angle_triangle_return_wit_8.
Axiom proof_of_right_angle_triangle_return_wit_9 : right_angle_triangle_return_wit_9.
Axiom proof_of_right_angle_triangle_return_wit_10 : right_angle_triangle_return_wit_10.
Axiom proof_of_right_angle_triangle_return_wit_11 : right_angle_triangle_return_wit_11.
Axiom proof_of_right_angle_triangle_return_wit_12 : right_angle_triangle_return_wit_12.
Axiom proof_of_right_angle_triangle_return_wit_13 : right_angle_triangle_return_wit_13.
Axiom proof_of_right_angle_triangle_return_wit_14 : right_angle_triangle_return_wit_14.
Axiom proof_of_right_angle_triangle_return_wit_15 : right_angle_triangle_return_wit_15.

End VC_Correct.
