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

(*----- Function is_prime -----*)

Definition is_prime_safety_wit_1 := 
forall (n_pre: Z) ,
  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_prime_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre < 2) |]
  &&  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre >= 2) |]
  &&  ((( &( "i" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int64  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_prime_safety_wit_4 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| (2 <= i) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "n" ) )) # Int64  |-> n)
|--
  [| ((i * i ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (i * i )) |]
.

Definition is_prime_safety_wit_5 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| ((i * i ) <= n) |] 
  &&  [| (2 <= i) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "n" ) )) # Int64  |-> n)
|--
  [| ((n <> (-9223372036854775808)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition is_prime_safety_wit_6 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| ((i * i ) <= n) |] 
  &&  [| (2 <= i) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "n" ) )) # Int64  |-> n)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_safety_wit_7 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| ((i * i ) <= n) |] 
  &&  [| (2 <= i) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "n" ) )) # Int64  |-> n)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_safety_wit_8 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| ((n % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= n) |] 
  &&  [| (2 <= i) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "n" ) )) # Int64  |-> n)
|--
  [| ((i + 1 ) <= 9223372036854775807) |] 
  &&  [| ((-9223372036854775808) <= (i + 1 )) |]
.

Definition is_prime_safety_wit_9 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| ((i * i ) > n) |] 
  &&  [| (2 <= i) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  ((( &( "i" ) )) # Int64  |-> i)
  **  ((( &( "n" ) )) # Int64  |-> n)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_prime_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre >= 2) |]
  &&  emp
|--
  [| (2 <= 2) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < 2)) -> ((n_pre % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  emp
.

Definition is_prime_entail_wit_2 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| ((n % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= n) |] 
  &&  [| (2 <= i) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < i)) -> ((n % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  emp
|--
  [| (2 <= (i + 1 )) |] 
  &&  [| forall (k: Z) , (((2 <= k) /\ (k < (i + 1 ))) -> ((n % ( k ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  emp
.

Definition is_prime_return_wit_1 := 
forall (n_pre: Z) (k_2: Z) (n: Z) (i: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| ((i * i ) <= n) |] 
  &&  [| (2 <= i) |] 
  &&  [| forall (k_3: Z) , (((2 <= k_3) /\ (k_3 < i)) -> ((n % ( k_3 ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  emp
|--
  [| ((0 = 1) -> ((n_pre >= 2) /\ forall (k: Z) , (((2 <= k) /\ (k < n_pre)) -> ((n_pre % ( k ) ) <> 0)))) |] 
  &&  [| ((0 = 0) -> ((n_pre < 2) \/ exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < n_pre)) /\ ((n_pre % ( k_2 ) ) = 0)))) |]
  &&  emp
.

Definition is_prime_return_wit_2 := 
forall (n_pre: Z) (k_2: Z) ,
  [| (n_pre < 2) |]
  &&  emp
|--
  [| ((0 = 1) -> ((n_pre >= 2) /\ forall (k: Z) , (((2 <= k) /\ (k < n_pre)) -> ((n_pre % ( k ) ) <> 0)))) |] 
  &&  [| ((0 = 0) -> ((n_pre < 2) \/ exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < n_pre)) /\ ((n_pre % ( k_2 ) ) = 0)))) |]
  &&  emp
.

Definition is_prime_return_wit_3 := 
forall (n_pre: Z) (k_2: Z) (n: Z) (i: Z) ,
  [| ((i * i ) > n) |] 
  &&  [| (2 <= i) |] 
  &&  [| forall (k_3: Z) , (((2 <= k_3) /\ (k_3 < i)) -> ((n % ( k_3 ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |]
  &&  emp
|--
  [| ((1 = 1) -> ((n_pre >= 2) /\ forall (k: Z) , (((2 <= k) /\ (k < n_pre)) -> ((n_pre % ( k ) ) <> 0)))) |] 
  &&  [| ((1 = 0) -> ((n_pre < 2) \/ exists (k_2: Z) , (((2 <= k_2) /\ (k_2 < n_pre)) /\ ((n_pre % ( k_2 ) ) = 0)))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_is_prime_safety_wit_1 : is_prime_safety_wit_1.
Axiom proof_of_is_prime_safety_wit_2 : is_prime_safety_wit_2.
Axiom proof_of_is_prime_safety_wit_3 : is_prime_safety_wit_3.
Axiom proof_of_is_prime_safety_wit_4 : is_prime_safety_wit_4.
Axiom proof_of_is_prime_safety_wit_5 : is_prime_safety_wit_5.
Axiom proof_of_is_prime_safety_wit_6 : is_prime_safety_wit_6.
Axiom proof_of_is_prime_safety_wit_7 : is_prime_safety_wit_7.
Axiom proof_of_is_prime_safety_wit_8 : is_prime_safety_wit_8.
Axiom proof_of_is_prime_safety_wit_9 : is_prime_safety_wit_9.
Axiom proof_of_is_prime_entail_wit_1 : is_prime_entail_wit_1.
Axiom proof_of_is_prime_entail_wit_2 : is_prime_entail_wit_2.
Axiom proof_of_is_prime_return_wit_1 : is_prime_return_wit_1.
Axiom proof_of_is_prime_return_wit_2 : is_prime_return_wit_2.
Axiom proof_of_is_prime_return_wit_3 : is_prime_return_wit_3.

End VC_Correct.
