Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_59.
Local Open Scope sac.

(*----- Function largest_prime_factor -----*)

Definition largest_prime_factor_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition largest_prime_factor_safety_wit_2 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| (2 <= i) |] 
  &&  [| (lpf_inv n_pre n i ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  [| ((n <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition largest_prime_factor_safety_wit_3 := 
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) ,
  [| (i >= 2) |] 
  &&  [| (lpf_while_inv n_pre n i ) |] 
  &&  [| (i_2 <= (n_2 ÷ i_2 )) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (lpf_inv n_pre n_2 i_2 ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  [| ((n <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition largest_prime_factor_safety_wit_4 := 
forall (n_pre: Z) (n: Z) (i: Z) (n_2: Z) (i_2: Z) ,
  [| (i_2 >= 2) |] 
  &&  [| (lpf_while_inv n_pre n_2 i_2 ) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (lpf_inv n_pre n i ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition largest_prime_factor_safety_wit_5 := 
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) ,
  [| (n_2 <= i) |] 
  &&  [| ((n_2 % ( i ) ) = 0) |] 
  &&  [| (i >= 2) |] 
  &&  [| (lpf_while_inv n_pre n_2 i ) |] 
  &&  [| (i_2 <= (n ÷ i_2 )) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (lpf_inv n_pre n i_2 ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_prime_factor_safety_wit_6 := 
forall (n_pre: Z) (n: Z) (i_2: Z) (n_2: Z) (i: Z) ,
  [| ((n_2 % ( i ) ) <> 0) |] 
  &&  [| (i >= 2) |] 
  &&  [| (lpf_while_inv n_pre n_2 i ) |] 
  &&  [| (i_2 <= (n ÷ i_2 )) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (lpf_inv n_pre n i_2 ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_2)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition largest_prime_factor_safety_wit_7 := 
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) ,
  [| (n > i) |] 
  &&  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i >= 2) |] 
  &&  [| (lpf_while_inv n_pre n i ) |] 
  &&  [| (i_2 <= (n_2 ÷ i_2 )) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (lpf_inv n_pre n_2 i_2 ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  [| ((n <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition largest_prime_factor_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (2 <= 2) |] 
  &&  [| (lpf_inv n_pre n_pre 2 ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition largest_prime_factor_entail_wit_2 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| (i <= (n ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (lpf_inv n_pre n i ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (i >= 2) |] 
  &&  [| (lpf_while_inv n_pre n i ) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (lpf_inv n_pre n i ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition largest_prime_factor_entail_wit_3_1 := 
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) ,
  [| ((n % ( i ) ) <> 0) |] 
  &&  [| (i >= 2) |] 
  &&  [| (lpf_while_inv n_pre n i ) |] 
  &&  [| (i_2 <= (n_2 ÷ i_2 )) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (lpf_inv n_pre n_2 i_2 ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (2 <= (i + 1 )) |] 
  &&  [| (lpf_inv n_pre n (i + 1 ) ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition largest_prime_factor_entail_wit_3_2 := 
forall (n_pre: Z) (n_2: Z) (i_2: Z) (n: Z) (i: Z) ,
  [| (n <= i) |] 
  &&  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i >= 2) |] 
  &&  [| (lpf_while_inv n_pre n i ) |] 
  &&  [| (i_2 <= (n_2 ÷ i_2 )) |] 
  &&  [| (2 <= i_2) |] 
  &&  [| (lpf_inv n_pre n_2 i_2 ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (2 <= (i + 1 )) |] 
  &&  [| (lpf_inv n_pre n (i + 1 ) ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition largest_prime_factor_entail_wit_4 := 
forall (n_pre: Z) (n: Z) (i: Z) (n_2: Z) (i_2: Z) ,
  [| (n_2 > i_2) |] 
  &&  [| ((n_2 % ( i_2 ) ) = 0) |] 
  &&  [| (i_2 >= 2) |] 
  &&  [| (lpf_while_inv n_pre n_2 i_2 ) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (lpf_inv n_pre n i ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (i_2 >= 2) |] 
  &&  [| (lpf_while_inv n_pre (n_2 ÷ i_2 ) i_2 ) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (lpf_inv n_pre n i ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
.

Definition largest_prime_factor_return_wit_1 := 
forall (n_pre: Z) (n: Z) (i: Z) ,
  [| (i > (n ÷ i )) |] 
  &&  [| (2 <= i) |] 
  &&  [| (lpf_inv n_pre n i ) |] 
  &&  [| (problem_59_pre n_pre ) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| (problem_59_spec n_pre n ) |]
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_largest_prime_factor_safety_wit_1 : largest_prime_factor_safety_wit_1.
Axiom proof_of_largest_prime_factor_safety_wit_2 : largest_prime_factor_safety_wit_2.
Axiom proof_of_largest_prime_factor_safety_wit_3 : largest_prime_factor_safety_wit_3.
Axiom proof_of_largest_prime_factor_safety_wit_4 : largest_prime_factor_safety_wit_4.
Axiom proof_of_largest_prime_factor_safety_wit_5 : largest_prime_factor_safety_wit_5.
Axiom proof_of_largest_prime_factor_safety_wit_6 : largest_prime_factor_safety_wit_6.
Axiom proof_of_largest_prime_factor_safety_wit_7 : largest_prime_factor_safety_wit_7.
Axiom proof_of_largest_prime_factor_entail_wit_1 : largest_prime_factor_entail_wit_1.
Axiom proof_of_largest_prime_factor_entail_wit_2 : largest_prime_factor_entail_wit_2.
Axiom proof_of_largest_prime_factor_entail_wit_3_1 : largest_prime_factor_entail_wit_3_1.
Axiom proof_of_largest_prime_factor_entail_wit_3_2 : largest_prime_factor_entail_wit_3_2.
Axiom proof_of_largest_prime_factor_entail_wit_4 : largest_prime_factor_entail_wit_4.
Axiom proof_of_largest_prime_factor_return_wit_1 : largest_prime_factor_return_wit_1.

End VC_Correct.
