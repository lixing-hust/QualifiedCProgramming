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

(*----- Function is_prime_simple -----*)

Definition is_prime_simple_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_prime_simple_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (n_pre < 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_simple_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition is_prime_simple_safety_wit_4 := 
forall (n_pre: Z) (d: Z) ,
  [| (d < n_pre) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < d)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre <> (INT_MIN)) \/ (d <> (-1))) |] 
  &&  [| (d <> 0) |]
.

Definition is_prime_simple_safety_wit_5 := 
forall (n_pre: Z) (d: Z) ,
  [| (d < n_pre) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < d)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_simple_safety_wit_6 := 
forall (n_pre: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) = 0) |] 
  &&  [| (d < n_pre) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < d)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition is_prime_simple_safety_wit_7 := 
forall (n_pre: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) <> 0) |] 
  &&  [| (d < n_pre) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < d)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((d + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (d + 1 )) |]
.

Definition is_prime_simple_safety_wit_8 := 
forall (n_pre: Z) (d: Z) ,
  [| (d >= n_pre) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < d)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition is_prime_simple_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < 2)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
.

Definition is_prime_simple_entail_wit_2 := 
forall (n_pre: Z) (d: Z) ,
  [| ((n_pre % ( d ) ) <> 0) |] 
  &&  [| (d < n_pre) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < d)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  [| (2 <= (d + 1 )) |] 
  &&  [| ((d + 1 ) <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < (d + 1 ))) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
.

Definition is_prime_simple_return_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre < 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  ([| (0 = 0) |] 
  &&  [| (n_pre < 2) |]
  &&  emp)
  ||
  (EX (d: Z) ,
  [| (0 = 0) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d < n_pre) |] 
  &&  [| ((n_pre % ( d ) ) = 0) |]
  &&  emp)
  ||
  ([| (0 = 1) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| forall (d_2: Z) , (((2 <= d_2) /\ (d_2 < n_pre)) -> ((n_pre % ( d_2 ) ) <> 0)) |]
  &&  emp)
.

Definition is_prime_simple_return_wit_2 := 
forall (n_pre: Z) (d_3: Z) ,
  [| ((n_pre % ( d_3 ) ) = 0) |] 
  &&  [| (d_3 < n_pre) |] 
  &&  [| (2 <= d_3) |] 
  &&  [| (d_3 <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < d_3)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  ([| (0 = 0) |] 
  &&  [| (n_pre < 2) |]
  &&  emp)
  ||
  (EX (d: Z) ,
  [| (0 = 0) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d < n_pre) |] 
  &&  [| ((n_pre % ( d ) ) = 0) |]
  &&  emp)
  ||
  ([| (0 = 1) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| forall (d_2: Z) , (((2 <= d_2) /\ (d_2 < n_pre)) -> ((n_pre % ( d_2 ) ) <> 0)) |]
  &&  emp)
.

Definition is_prime_simple_return_wit_3 := 
forall (n_pre: Z) (d_3: Z) ,
  [| (d_3 >= n_pre) |] 
  &&  [| (2 <= d_3) |] 
  &&  [| (d_3 <= n_pre) |] 
  &&  [| forall (i: Z) , (((2 <= i) /\ (i < d_3)) -> ((n_pre % ( i ) ) <> 0)) |] 
  &&  [| (n_pre >= 2) |] 
  &&  [| (0 <= n_pre) |]
  &&  emp
|--
  ([| (1 = 0) |] 
  &&  [| (n_pre < 2) |]
  &&  emp)
  ||
  (EX (d: Z) ,
  [| (1 = 0) |] 
  &&  [| (2 <= d) |] 
  &&  [| (d < n_pre) |] 
  &&  [| ((n_pre % ( d ) ) = 0) |]
  &&  emp)
  ||
  ([| (1 = 1) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| forall (d_2: Z) , (((2 <= d_2) /\ (d_2 < n_pre)) -> ((n_pre % ( d_2 ) ) <> 0)) |]
  &&  emp)
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_is_prime_simple_safety_wit_1 : is_prime_simple_safety_wit_1.
Axiom proof_of_is_prime_simple_safety_wit_2 : is_prime_simple_safety_wit_2.
Axiom proof_of_is_prime_simple_safety_wit_3 : is_prime_simple_safety_wit_3.
Axiom proof_of_is_prime_simple_safety_wit_4 : is_prime_simple_safety_wit_4.
Axiom proof_of_is_prime_simple_safety_wit_5 : is_prime_simple_safety_wit_5.
Axiom proof_of_is_prime_simple_safety_wit_6 : is_prime_simple_safety_wit_6.
Axiom proof_of_is_prime_simple_safety_wit_7 : is_prime_simple_safety_wit_7.
Axiom proof_of_is_prime_simple_safety_wit_8 : is_prime_simple_safety_wit_8.
Axiom proof_of_is_prime_simple_entail_wit_1 : is_prime_simple_entail_wit_1.
Axiom proof_of_is_prime_simple_entail_wit_2 : is_prime_simple_entail_wit_2.
Axiom proof_of_is_prime_simple_return_wit_1 : is_prime_simple_return_wit_1.
Axiom proof_of_is_prime_simple_return_wit_2 : is_prime_simple_return_wit_2.
Axiom proof_of_is_prime_simple_return_wit_3 : is_prime_simple_return_wit_3.

End VC_Correct.
