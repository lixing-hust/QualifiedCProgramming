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
Require Import coins_138.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function is_equal_to_sum_even -----*)

Definition is_equal_to_sum_even_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition is_equal_to_sum_even_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_equal_to_sum_even_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_equal_to_sum_even_safety_wit_4 := 
forall (n_pre: Z) ,
  [| ((n_pre % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (8 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 8) |]
.

Definition is_equal_to_sum_even_safety_wit_5 := 
forall (n_pre: Z) ,
  [| (n_pre >= 8) |] 
  &&  [| ((n_pre % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_equal_to_sum_even_safety_wit_6 := 
forall (n_pre: Z) ,
  [| (n_pre < 8) |] 
  &&  [| ((n_pre % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_equal_to_sum_even_safety_wit_7 := 
forall (n_pre: Z) ,
  [| ((n_pre % ( 2 ) ) <> 0) |] 
  &&  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_equal_to_sum_even_return_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre >= 8) |] 
  &&  [| ((n_pre % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_138_spec_z n_pre 1 ) |]
  &&  emp
.

Definition is_equal_to_sum_even_return_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre < 8) |] 
  &&  [| ((n_pre % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_138_spec_z n_pre 0 ) |]
  &&  emp
.

Definition is_equal_to_sum_even_return_wit_3 := 
forall (n_pre: Z) ,
  [| ((n_pre % ( 2 ) ) <> 0) |] 
  &&  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_138_spec_z n_pre 0 ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_is_equal_to_sum_even_safety_wit_1 : is_equal_to_sum_even_safety_wit_1.
Axiom proof_of_is_equal_to_sum_even_safety_wit_2 : is_equal_to_sum_even_safety_wit_2.
Axiom proof_of_is_equal_to_sum_even_safety_wit_3 : is_equal_to_sum_even_safety_wit_3.
Axiom proof_of_is_equal_to_sum_even_safety_wit_4 : is_equal_to_sum_even_safety_wit_4.
Axiom proof_of_is_equal_to_sum_even_safety_wit_5 : is_equal_to_sum_even_safety_wit_5.
Axiom proof_of_is_equal_to_sum_even_safety_wit_6 : is_equal_to_sum_even_safety_wit_6.
Axiom proof_of_is_equal_to_sum_even_safety_wit_7 : is_equal_to_sum_even_safety_wit_7.
Axiom proof_of_is_equal_to_sum_even_return_wit_1 : is_equal_to_sum_even_return_wit_1.
Axiom proof_of_is_equal_to_sum_even_return_wit_2 : is_equal_to_sum_even_return_wit_2.
Axiom proof_of_is_equal_to_sum_even_return_wit_3 : is_equal_to_sum_even_return_wit_3.

End VC_Correct.
