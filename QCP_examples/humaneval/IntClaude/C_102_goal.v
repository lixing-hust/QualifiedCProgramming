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
Require Import coins_102.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function choose_num -----*)

Definition choose_num_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre < x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <> (INT_MIN)) |]
.

Definition choose_num_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre < x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition choose_num_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((y_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition choose_num_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition choose_num_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition choose_num_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <> (INT_MIN)) |]
.

Definition choose_num_safety_wit_7 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition choose_num_safety_wit_8 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((y_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition choose_num_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition choose_num_safety_wit_10 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition choose_num_safety_wit_11 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| False |]
.

Definition choose_num_safety_wit_12 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre <> x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((y_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition choose_num_safety_wit_13 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre <> x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition choose_num_safety_wit_14 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre <> x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition choose_num_safety_wit_15 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| ((y_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (y_pre - 1 )) |]
.

Definition choose_num_safety_wit_16 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition choose_num_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| (y_pre < x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_102_spec x_pre y_pre (-1) ) |]
  &&  emp
.

Definition choose_num_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_102_spec x_pre y_pre (-1) ) |]
  &&  emp
.

Definition choose_num_return_wit_3 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) = 1) |] 
  &&  [| (y_pre <> x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_102_spec x_pre y_pre (y_pre - 1 ) ) |]
  &&  emp
.

Definition choose_num_return_wit_4 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre = x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_102_spec x_pre y_pre y_pre ) |]
  &&  emp
.

Definition choose_num_return_wit_5 := 
forall (y_pre: Z) (x_pre: Z) ,
  [| ((y_pre % ( 2 ) ) <> 1) |] 
  &&  [| (y_pre <> x_pre) |] 
  &&  [| (y_pre >= x_pre) |] 
  &&  [| (problem_102_pre x_pre y_pre ) |] 
  &&  [| (1 <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (1 <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_102_spec x_pre y_pre y_pre ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_choose_num_safety_wit_1 : choose_num_safety_wit_1.
Axiom proof_of_choose_num_safety_wit_2 : choose_num_safety_wit_2.
Axiom proof_of_choose_num_safety_wit_3 : choose_num_safety_wit_3.
Axiom proof_of_choose_num_safety_wit_4 : choose_num_safety_wit_4.
Axiom proof_of_choose_num_safety_wit_5 : choose_num_safety_wit_5.
Axiom proof_of_choose_num_safety_wit_6 : choose_num_safety_wit_6.
Axiom proof_of_choose_num_safety_wit_7 : choose_num_safety_wit_7.
Axiom proof_of_choose_num_safety_wit_8 : choose_num_safety_wit_8.
Axiom proof_of_choose_num_safety_wit_9 : choose_num_safety_wit_9.
Axiom proof_of_choose_num_safety_wit_10 : choose_num_safety_wit_10.
Axiom proof_of_choose_num_safety_wit_11 : choose_num_safety_wit_11.
Axiom proof_of_choose_num_safety_wit_12 : choose_num_safety_wit_12.
Axiom proof_of_choose_num_safety_wit_13 : choose_num_safety_wit_13.
Axiom proof_of_choose_num_safety_wit_14 : choose_num_safety_wit_14.
Axiom proof_of_choose_num_safety_wit_15 : choose_num_safety_wit_15.
Axiom proof_of_choose_num_safety_wit_16 : choose_num_safety_wit_16.
Axiom proof_of_choose_num_return_wit_1 : choose_num_return_wit_1.
Axiom proof_of_choose_num_return_wit_2 : choose_num_return_wit_2.
Axiom proof_of_choose_num_return_wit_3 : choose_num_return_wit_3.
Axiom proof_of_choose_num_return_wit_4 : choose_num_return_wit_4.
Axiom proof_of_choose_num_return_wit_5 : choose_num_return_wit_5.

End VC_Correct.
