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

(*----- Function prime_fib -----*)

Definition prime_fib_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |->_)
  **  ((( &( "f1" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition prime_fib_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |->_)
  **  ((( &( "f1" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition prime_fib_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |-> 2)
  **  ((( &( "f1" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prime_fib_safety_wit_4 := 
forall (n_pre: Z) (count: Z) ,
  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |-> 2)
  **  ((( &( "f1" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((1 + 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (1 + 2 )) |]
.

Definition prime_fib_safety_wit_5 := 
forall (n_pre: Z) (count: Z) ,
  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "isprime" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition prime_fib_safety_wit_6 := 
forall (n_pre: Z) (count: Z) ,
  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition prime_fib_safety_wit_7 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((w * w ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (w * w )) |]
.

Definition prime_fib_safety_wit_8 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((w * w ) <= 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((2 <> (INT_MIN)) \/ (w <> (-1))) |] 
  &&  [| (w <> 0) |]
.

Definition prime_fib_safety_wit_9 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((w * w ) <= 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prime_fib_safety_wit_10 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((2 % ( w ) ) = 0) |] 
  &&  [| ((w * w ) <= 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prime_fib_safety_wit_11 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((2 % ( w ) ) <> 0) |] 
  &&  [| ((w * w ) <= 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((w + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (w + 1 )) |]
.

Definition prime_fib_safety_wit_12 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((w * w ) > 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition prime_fib_safety_wit_13 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((w * w ) > 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition prime_fib_safety_wit_14 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| (count = n_pre) |] 
  &&  [| ((2 % ( w ) ) = 0) |] 
  &&  [| ((w * w ) <= 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> 0)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| False |]
.

Definition prime_fib_safety_wit_15 := 
forall (n_pre: Z) (count: Z) ,
  [| (count >= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |-> 2)
  **  ((( &( "f1" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prime_fib_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
.

Definition prime_fib_entail_wit_2 := 
forall (n_pre: Z) (count: Z) ,
  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (2 <= 2) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
.

Definition prime_fib_entail_wit_3 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((2 % ( w ) ) <> 0) |] 
  &&  [| ((w * w ) <= 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (2 <= (w + 1 )) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
.

Definition prime_fib_entail_wit_4_1 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((count + 1 ) <> n_pre) |] 
  &&  [| ((w * w ) > 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
|--
  [| (0 <= (count + 1 )) |] 
  &&  [| ((count + 1 ) <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |-> 2)
  **  ((( &( "f1" ) )) # Int  |-> 1)
.

Definition prime_fib_entail_wit_4_2 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| (count <> n_pre) |] 
  &&  [| ((2 % ( w ) ) = 0) |] 
  &&  [| ((w * w ) <= 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f2" ) )) # Int  |-> (1 + 2 ))
  **  ((( &( "f1" ) )) # Int  |-> 2)
|--
  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |-> 2)
  **  ((( &( "f1" ) )) # Int  |-> 1)
.

Definition prime_fib_return_wit_1 := 
forall (n_pre: Z) (count: Z) (w: Z) ,
  [| ((count + 1 ) = n_pre) |] 
  &&  [| ((w * w ) > 2) |] 
  &&  [| (2 <= w) |] 
  &&  [| (count < n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (2 = (prime_fib_coq (n_pre))) |]
  &&  emp
.

Definition prime_fib_return_wit_2 := 
forall (n_pre: Z) (count: Z) ,
  [| (count >= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= n_pre) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |]
  &&  emp
|--
  [| (0 = (prime_fib_coq (n_pre))) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_prime_fib_safety_wit_1 : prime_fib_safety_wit_1.
Axiom proof_of_prime_fib_safety_wit_2 : prime_fib_safety_wit_2.
Axiom proof_of_prime_fib_safety_wit_3 : prime_fib_safety_wit_3.
Axiom proof_of_prime_fib_safety_wit_4 : prime_fib_safety_wit_4.
Axiom proof_of_prime_fib_safety_wit_5 : prime_fib_safety_wit_5.
Axiom proof_of_prime_fib_safety_wit_6 : prime_fib_safety_wit_6.
Axiom proof_of_prime_fib_safety_wit_7 : prime_fib_safety_wit_7.
Axiom proof_of_prime_fib_safety_wit_8 : prime_fib_safety_wit_8.
Axiom proof_of_prime_fib_safety_wit_9 : prime_fib_safety_wit_9.
Axiom proof_of_prime_fib_safety_wit_10 : prime_fib_safety_wit_10.
Axiom proof_of_prime_fib_safety_wit_11 : prime_fib_safety_wit_11.
Axiom proof_of_prime_fib_safety_wit_12 : prime_fib_safety_wit_12.
Axiom proof_of_prime_fib_safety_wit_13 : prime_fib_safety_wit_13.
Axiom proof_of_prime_fib_safety_wit_14 : prime_fib_safety_wit_14.
Axiom proof_of_prime_fib_safety_wit_15 : prime_fib_safety_wit_15.
Axiom proof_of_prime_fib_entail_wit_1 : prime_fib_entail_wit_1.
Axiom proof_of_prime_fib_entail_wit_2 : prime_fib_entail_wit_2.
Axiom proof_of_prime_fib_entail_wit_3 : prime_fib_entail_wit_3.
Axiom proof_of_prime_fib_entail_wit_4_1 : prime_fib_entail_wit_4_1.
Axiom proof_of_prime_fib_entail_wit_4_2 : prime_fib_entail_wit_4_2.
Axiom proof_of_prime_fib_return_wit_1 : prime_fib_return_wit_1.
Axiom proof_of_prime_fib_return_wit_2 : prime_fib_return_wit_2.

End VC_Correct.
