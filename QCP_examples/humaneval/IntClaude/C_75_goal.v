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
Require Import coins_75.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function is_multiply_prime -----*)

Definition is_multiply_prime_safety_wit_1 := 
forall (a_pre: Z) ,
  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_multiply_prime_safety_wit_2 := 
forall (a_pre: Z) ,
  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_multiply_prime_safety_wit_3 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) ,
  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| ((i * i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * i )) |]
.

Definition is_multiply_prime_safety_wit_4 := 
forall (a_pre: Z) (num: Z) (a_2: Z) (i_2: Z) (num_2: Z) (i: Z) (a: Z) ,
  [| (a >= 1) |] 
  &&  [| (i >= 2) |] 
  &&  [| (0 <= num_2) |] 
  &&  [| (num_2 <= 2) |] 
  &&  [| ((a % ( i ) ) <> 0) |] 
  &&  [| ((i_2 * i_2 ) <= a_2) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (a_2 >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  [| ((a <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition is_multiply_prime_safety_wit_5 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) ,
  [| (a_2 >= 1) |] 
  &&  [| (i_2 >= 2) |] 
  &&  [| (0 <= num_2) |] 
  &&  [| (num_2 <= 2) |] 
  &&  [| ((a_2 % ( i_2 ) ) <> 0) |] 
  &&  [| ((i * i ) <= a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "a" ) )) # Int  |-> a_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_multiply_prime_safety_wit_6 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) (num_2: Z) (i_2: Z) (a_2: Z) ,
  [| ((a_2 % ( i_2 ) ) = 0) |] 
  &&  [| (a_2 >= 1) |] 
  &&  [| (i_2 >= 2) |] 
  &&  [| (0 <= num_2) |] 
  &&  [| (num_2 <= 2) |] 
  &&  [| ((a_2 % ( i_2 ) ) <> 0) |] 
  &&  [| ((i * i ) <= a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "a" ) )) # Int  |-> a_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  [| False |]
.

Definition is_multiply_prime_safety_wit_7 := 
forall (a_pre: Z) (num: Z) (a: Z) (i_2: Z) (num_2: Z) (i: Z) (a_2: Z) ,
  [| ((a_2 % ( i ) ) <> 0) |] 
  &&  [| (a_2 >= 1) |] 
  &&  [| (i >= 2) |] 
  &&  [| (0 <= num_2) |] 
  &&  [| (num_2 <= 2) |] 
  &&  [| ((a_2 % ( i ) ) <> 0) |] 
  &&  [| ((i_2 * i_2 ) <= a) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "a" ) )) # Int  |-> a_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num_2)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition is_multiply_prime_safety_wit_8 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) ,
  [| ((i * i ) > a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_multiply_prime_safety_wit_9 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) ,
  [| (num = 2) |] 
  &&  [| ((i * i ) > a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_multiply_prime_safety_wit_10 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) ,
  [| (num <> 2) |] 
  &&  [| ((i * i ) > a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_multiply_prime_entail_wit_1 := 
forall (a_pre: Z) ,
  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  emp
|--
  [| (2 <= 2) |] 
  &&  [| (a_pre >= 1) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  emp
.

Definition is_multiply_prime_entail_wit_2 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) ,
  [| ((i * i ) <= a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  emp
|--
  [| (a >= 1) |] 
  &&  [| (i >= 2) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| ((a % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  emp
.

Definition is_multiply_prime_entail_wit_3 := 
forall (a_pre: Z) (num_2: Z) (a_2: Z) (i_2: Z) (num: Z) (i: Z) (a: Z) ,
  [| ((a % ( i ) ) <> 0) |] 
  &&  [| (a >= 1) |] 
  &&  [| (i >= 2) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| ((a % ( i ) ) <> 0) |] 
  &&  [| ((i_2 * i_2 ) <= a_2) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (a_2 >= 1) |] 
  &&  [| (0 <= num_2) |] 
  &&  [| (num_2 <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  emp
|--
  [| (2 <= (i + 1 )) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  emp
.

Definition is_multiply_prime_return_wit_1 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) ,
  [| (num = 2) |] 
  &&  [| ((i * i ) > a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  emp
|--
  [| (problem_75_spec_z a_pre 1 ) |]
  &&  emp
.

Definition is_multiply_prime_return_wit_2 := 
forall (a_pre: Z) (num: Z) (a: Z) (i: Z) ,
  [| (num <> 2) |] 
  &&  [| ((i * i ) > a) |] 
  &&  [| (2 <= i) |] 
  &&  [| (a >= 1) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= 2) |] 
  &&  [| (problem_75_pre a_pre ) |] 
  &&  [| (2 <= a_pre) |] 
  &&  [| (a_pre < 100) |]
  &&  emp
|--
  [| (problem_75_spec_z a_pre 0 ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_is_multiply_prime_safety_wit_1 : is_multiply_prime_safety_wit_1.
Axiom proof_of_is_multiply_prime_safety_wit_2 : is_multiply_prime_safety_wit_2.
Axiom proof_of_is_multiply_prime_safety_wit_3 : is_multiply_prime_safety_wit_3.
Axiom proof_of_is_multiply_prime_safety_wit_4 : is_multiply_prime_safety_wit_4.
Axiom proof_of_is_multiply_prime_safety_wit_5 : is_multiply_prime_safety_wit_5.
Axiom proof_of_is_multiply_prime_safety_wit_6 : is_multiply_prime_safety_wit_6.
Axiom proof_of_is_multiply_prime_safety_wit_7 : is_multiply_prime_safety_wit_7.
Axiom proof_of_is_multiply_prime_safety_wit_8 : is_multiply_prime_safety_wit_8.
Axiom proof_of_is_multiply_prime_safety_wit_9 : is_multiply_prime_safety_wit_9.
Axiom proof_of_is_multiply_prime_safety_wit_10 : is_multiply_prime_safety_wit_10.
Axiom proof_of_is_multiply_prime_entail_wit_1 : is_multiply_prime_entail_wit_1.
Axiom proof_of_is_multiply_prime_entail_wit_2 : is_multiply_prime_entail_wit_2.
Axiom proof_of_is_multiply_prime_entail_wit_3 : is_multiply_prime_entail_wit_3.
Axiom proof_of_is_multiply_prime_return_wit_1 : is_multiply_prime_return_wit_1.
Axiom proof_of_is_multiply_prime_return_wit_2 : is_multiply_prime_return_wit_2.

End VC_Correct.
