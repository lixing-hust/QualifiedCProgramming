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
Require Import coins_150.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.

(*----- Function x_or_y -----*)

Definition x_or_y_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) ,
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "isp" ) )) # Int  |->_)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition x_or_y_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) ,
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition x_or_y_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) ,
  [| (n_pre < 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| False |]
.

Definition x_or_y_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) ,
  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition x_or_y_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition x_or_y_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| (i <= (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition x_or_y_safety_wit_7 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| (i <= (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition x_or_y_safety_wit_8 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| ((n_pre % ( i ) ) = 0) |] 
  &&  [| (i <= (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition x_or_y_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| ((n_pre % ( i ) ) <> 0) |] 
  &&  [| (i <= (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition x_or_y_safety_wit_10 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| ((n_pre % ( i ) ) = 0) |] 
  &&  [| (i <= (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "isp" ) )) # Int  |-> 0)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition x_or_y_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) ,
  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| ((1 <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < 2)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((1 = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < 2)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
.

Definition x_or_y_entail_wit_2_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| ((n_pre % ( i ) ) = 0) |] 
  &&  [| (i <= (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((0 <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < (i + 1 ))) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((0 = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
.

Definition x_or_y_entail_wit_2_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| ((n_pre % ( i ) ) <> 0) |] 
  &&  [| (i <= (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
|--
  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < (i + 1 ))) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < (i + 1 ))) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |]
  &&  emp
.

Definition x_or_y_return_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| (i > (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |] 
  &&  [| (isp <> 0) |]
  &&  emp
|--
  [| (problem_150_spec_z n_pre x_pre y_pre x_pre ) |]
  &&  emp
.

Definition x_or_y_return_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (n_pre: Z) (k_2: Z) (isp: Z) (i: Z) ,
  [| (i > (n_pre ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| ((isp <> 0) -> forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n_pre % ( k ) ) <> 0))) |] 
  &&  [| ((isp = 0) -> exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < i)) /\ ((n_pre % ( k_2 ) ) = 0))) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |] 
  &&  [| (INT_MIN <= y_pre) |] 
  &&  [| (y_pre <= INT_MAX) |] 
  &&  [| (isp = 0) |]
  &&  emp
|--
  [| (problem_150_spec_z n_pre x_pre y_pre y_pre ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_x_or_y_safety_wit_1 : x_or_y_safety_wit_1.
Axiom proof_of_x_or_y_safety_wit_2 : x_or_y_safety_wit_2.
Axiom proof_of_x_or_y_safety_wit_3 : x_or_y_safety_wit_3.
Axiom proof_of_x_or_y_safety_wit_4 : x_or_y_safety_wit_4.
Axiom proof_of_x_or_y_safety_wit_5 : x_or_y_safety_wit_5.
Axiom proof_of_x_or_y_safety_wit_6 : x_or_y_safety_wit_6.
Axiom proof_of_x_or_y_safety_wit_7 : x_or_y_safety_wit_7.
Axiom proof_of_x_or_y_safety_wit_8 : x_or_y_safety_wit_8.
Axiom proof_of_x_or_y_safety_wit_9 : x_or_y_safety_wit_9.
Axiom proof_of_x_or_y_safety_wit_10 : x_or_y_safety_wit_10.
Axiom proof_of_x_or_y_entail_wit_1 : x_or_y_entail_wit_1.
Axiom proof_of_x_or_y_entail_wit_2_1 : x_or_y_entail_wit_2_1.
Axiom proof_of_x_or_y_entail_wit_2_2 : x_or_y_entail_wit_2_2.
Axiom proof_of_x_or_y_return_wit_1 : x_or_y_return_wit_1.
Axiom proof_of_x_or_y_return_wit_2 : x_or_y_return_wit_2.

End VC_Correct.
