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

(*----- Function largest_divisor -----*)

Definition largest_divisor_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition largest_divisor_safety_wit_2 := 
forall (n_pre: Z) (i: Z) ,
  [| (2 <= i) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i * i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * i )) |]
.

Definition largest_divisor_safety_wit_3 := 
forall (n_pre: Z) (i: Z) ,
  [| ((i * i ) <= n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition largest_divisor_safety_wit_4 := 
forall (n_pre: Z) (i: Z) ,
  [| ((i * i ) <= n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_divisor_safety_wit_5 := 
forall (n_pre: Z) (i: Z) ,
  [| ((n_pre % ( i ) ) = 0) |] 
  &&  [| ((i * i ) <= n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition largest_divisor_safety_wit_6 := 
forall (n_pre: Z) (i: Z) ,
  [| ((n_pre % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_divisor_safety_wit_7 := 
forall (n_pre: Z) (i: Z) ,
  [| ((i * i ) > n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition largest_divisor_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition largest_divisor_entail_wit_2 := 
forall (n_pre: Z) (i: Z) ,
  [| ((n_pre % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= n_pre) |] 
  &&  [| (2 <= i) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (2 <= (i + 1 )) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition largest_divisor_return_wit_1 := 
forall (n_pre: Z) (i_2: Z) ,
  [| ((n_pre % ( i_2 ) ) = 0) |] 
  &&  [| ((i_2 * i_2 ) <= n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((n_pre % ( (n_pre ÷ i_2 ) ) ) = 0) |] 
  &&  [| ((n_pre ÷ i_2 ) < n_pre) |] 
  &&  [| forall (i: Z) , ((((0 < i) /\ (i < n_pre)) /\ ((n_pre % ( i ) ) = 0)) -> (i <= (n_pre ÷ i_2 ))) |]
  &&  emp
.

Definition largest_divisor_return_wit_2 := 
forall (n_pre: Z) (i_2: Z) ,
  [| ((i_2 * i_2 ) > n_pre) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((n_pre % ( 1 ) ) = 0) |] 
  &&  [| (1 < n_pre) |] 
  &&  [| forall (i: Z) , ((((0 < i) /\ (i < n_pre)) /\ ((n_pre % ( i ) ) = 0)) -> (i <= 1)) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_largest_divisor_safety_wit_1 : largest_divisor_safety_wit_1.
Axiom proof_of_largest_divisor_safety_wit_2 : largest_divisor_safety_wit_2.
Axiom proof_of_largest_divisor_safety_wit_3 : largest_divisor_safety_wit_3.
Axiom proof_of_largest_divisor_safety_wit_4 : largest_divisor_safety_wit_4.
Axiom proof_of_largest_divisor_safety_wit_5 : largest_divisor_safety_wit_5.
Axiom proof_of_largest_divisor_safety_wit_6 : largest_divisor_safety_wit_6.
Axiom proof_of_largest_divisor_safety_wit_7 : largest_divisor_safety_wit_7.
Axiom proof_of_largest_divisor_entail_wit_1 : largest_divisor_entail_wit_1.
Axiom proof_of_largest_divisor_entail_wit_2 : largest_divisor_entail_wit_2.
Axiom proof_of_largest_divisor_return_wit_1 : largest_divisor_return_wit_1.
Axiom proof_of_largest_divisor_return_wit_2 : largest_divisor_return_wit_2.

End VC_Correct.
