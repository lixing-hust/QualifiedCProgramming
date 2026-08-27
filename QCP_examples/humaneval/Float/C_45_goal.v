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
Require Import coins_45.
Local Open Scope sac.

(*----- Function triangle_area -----*)

Definition triangle_area_safety_wit_1 := 
(
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  ((( &( "area" ) )) # Float  |->_)
  **  ((( &( "h" ) )) # Float  |-> h_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_mul (a_pre) (h_pre))) ((fp32_of_real (0.5)))) ) ”
) \/
(
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  ((( &( "area" ) )) # Float  |->_)
  **  ((( &( "h" ) )) # Float  |-> h_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_mul (a_pre) (h_pre))) ((fp32_of_real (0.5)))) ) ”
).

Definition triangle_area_safety_wit_1_split_goal_1 := 
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  ((( &( "area" ) )) # Float  |->_)
  **  ((( &( "h" ) )) # Float  |-> h_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_mul (a_pre) (h_pre))) ((fp32_of_real (0.5)))) ) ”
.

Definition triangle_area_safety_wit_2 := 
(
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  ((( &( "area" ) )) # Float  |->_)
  **  ((( &( "h" ) )) # Float  |-> h_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (a_pre) (h_pre)) ) ”
) \/
(
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  ((( &( "area" ) )) # Float  |->_)
  **  ((( &( "h" ) )) # Float  |-> h_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (a_pre) (h_pre)) ) ”
).

Definition triangle_area_safety_wit_2_split_goal_1 := 
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  ((( &( "area" ) )) # Float  |->_)
  **  ((( &( "h" ) )) # Float  |-> h_pre)
  **  ((( &( "a" ) )) # Float  |-> a_pre)
|--
  “ (fp32_isFinite (fp32_mul (a_pre) (h_pre)) ) ”
.

Definition triangle_area_return_wit_1 := 
(
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_mul ((fp32_mul (a_pre) (h_pre))) ((fp32_of_real (0.5)))) (triangle_area_fp32 (a_pre) (h_pre))) ”
  &&  emp
) \/
(
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_mul ((fp32_mul (a_pre) (h_pre))) ((fp32_of_real (0.5)))) (triangle_area_fp32 (a_pre) (h_pre))) ”
  &&  emp
).

Definition triangle_area_return_wit_1_split_goal_1 := 
forall (h_pre: fp32) (a_pre: fp32) (PreH1 : (problem_45_pre a_pre h_pre )) ,
  (fp32_eq (fp32_mul ((fp32_mul (a_pre) (h_pre))) ((fp32_of_real (0.5)))) (triangle_area_fp32 (a_pre) (h_pre)))
.

Module Type VC_Correct.


Axiom proof_of_triangle_area_safety_wit_1 : triangle_area_safety_wit_1.
Axiom proof_of_triangle_area_safety_wit_2 : triangle_area_safety_wit_2.
Axiom proof_of_triangle_area_return_wit_1 : triangle_area_return_wit_1.

End VC_Correct.
