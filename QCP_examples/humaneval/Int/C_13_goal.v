Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function greatest_common_divisor -----*)

Definition greatest_common_divisor_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "m" ) )) # Int  |->_)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition greatest_common_divisor_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| (a < b) |] 
  &&  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Int  |-> a)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "m" ) )) # Int  |-> a)
|--
  [| ((b <> (INT_MIN)) \/ (a <> (-1))) |] 
  &&  [| (a <> 0) |]
.

Definition greatest_common_divisor_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| (a >= b) |] 
  &&  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "m" ) )) # Int  |->_)
|--
  [| ((a <> (INT_MIN)) \/ (b <> (-1))) |] 
  &&  [| (b <> 0) |]
.

Definition greatest_common_divisor_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| (a >= b) |] 
  &&  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> (a % ( b ) ))
  **  ((( &( "m" ) )) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition greatest_common_divisor_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| (a < b) |] 
  &&  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "b" ) )) # Int  |-> a)
  **  ((( &( "a" ) )) # Int  |-> (b % ( a ) ))
  **  ((( &( "m" ) )) # Int  |-> a)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition greatest_common_divisor_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) ,
  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((Zgcd (a_pre) (b_pre)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a_pre >= 0) |] 
  &&  [| (b_pre > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
.

Definition greatest_common_divisor_entail_wit_2_1 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| ((a % ( b ) ) <> 0) |] 
  &&  [| (a >= b) |] 
  &&  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((Zgcd ((a % ( b ) )) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| ((a % ( b ) ) >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
.

Definition greatest_common_divisor_entail_wit_2_2 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| ((b % ( a ) ) <> 0) |] 
  &&  [| (a < b) |] 
  &&  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |-> a)
|--
  [| ((Zgcd ((b % ( a ) )) (a)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| ((b % ( a ) ) >= 0) |] 
  &&  [| (a > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |->_)
.

Definition greatest_common_divisor_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| ((a % ( b ) ) = 0) |] 
  &&  [| (a >= b) |] 
  &&  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
|--
  [| (b = (Zgcd (a_pre) (b_pre))) |]
  &&  emp
.

Definition greatest_common_divisor_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (a: Z) (b: Z) ,
  [| ((b % ( a ) ) = 0) |] 
  &&  [| (a < b) |] 
  &&  [| ((Zgcd (a) (b)) = (Zgcd (a_pre) (b_pre))) |] 
  &&  [| (a >= 0) |] 
  &&  [| (b > 0) |] 
  &&  [| (INT_MIN < a_pre) |] 
  &&  [| (a_pre <= INT_MAX) |] 
  &&  [| (INT_MIN < b_pre) |] 
  &&  [| (b_pre <= INT_MAX) |]
  &&  emp
|--
  [| (a = (Zgcd (a_pre) (b_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_greatest_common_divisor_safety_wit_1 : greatest_common_divisor_safety_wit_1.
Axiom proof_of_greatest_common_divisor_safety_wit_2 : greatest_common_divisor_safety_wit_2.
Axiom proof_of_greatest_common_divisor_safety_wit_3 : greatest_common_divisor_safety_wit_3.
Axiom proof_of_greatest_common_divisor_safety_wit_4 : greatest_common_divisor_safety_wit_4.
Axiom proof_of_greatest_common_divisor_safety_wit_5 : greatest_common_divisor_safety_wit_5.
Axiom proof_of_greatest_common_divisor_entail_wit_1 : greatest_common_divisor_entail_wit_1.
Axiom proof_of_greatest_common_divisor_entail_wit_2_1 : greatest_common_divisor_entail_wit_2_1.
Axiom proof_of_greatest_common_divisor_entail_wit_2_2 : greatest_common_divisor_entail_wit_2_2.
Axiom proof_of_greatest_common_divisor_return_wit_1 : greatest_common_divisor_return_wit_1.
Axiom proof_of_greatest_common_divisor_return_wit_2 : greatest_common_divisor_return_wit_2.

End VC_Correct.
