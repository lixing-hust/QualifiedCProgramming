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
Require Import coins_49.
Local Open Scope sac.

(*----- Function modp -----*)

Definition modp_safety_wit_1 := 
forall (p_pre: Z) (n_pre: Z) ,
  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  ((( &( "out" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition modp_safety_wit_2 := 
forall (p_pre: Z) (n_pre: Z) ,
  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |-> 1)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition modp_safety_wit_3 := 
forall (p_pre: Z) (n_pre: Z) (out: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out = ((2^i) % ( p_pre ) )) |] 
  &&  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> ((out * 2 ) % ( p_pre ) ))
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition modp_safety_wit_4 := 
forall (p_pre: Z) (n_pre: Z) (out: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out = ((2^i) % ( p_pre ) )) |] 
  &&  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((out * 2 ) <> (INT_MIN)) \/ (p_pre <> (-1))) |] 
  &&  [| (p_pre <> 0) |]
.

Definition modp_safety_wit_5 := 
forall (p_pre: Z) (n_pre: Z) (out: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out = ((2^i) % ( p_pre ) )) |] 
  &&  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((out * 2 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (out * 2 )) |]
.

Definition modp_safety_wit_6 := 
forall (p_pre: Z) (n_pre: Z) (out: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out = ((2^i) % ( p_pre ) )) |] 
  &&  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition modp_entail_wit_1 := 
forall (p_pre: Z) (n_pre: Z) ,
  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  emp
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (1 = ((2^0) % ( p_pre ) )) |] 
  &&  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  emp
.

Definition modp_entail_wit_2 := 
forall (p_pre: Z) (n_pre: Z) (out: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out = ((2^i) % ( p_pre ) )) |] 
  &&  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  emp
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (((out * 2 ) % ( p_pre ) ) = ((2^(i + 1 )) % ( p_pre ) )) |] 
  &&  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  emp
.

Definition modp_return_wit_1 := 
forall (p_pre: Z) (n_pre: Z) (out: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (out = ((2^i) % ( p_pre ) )) |] 
  &&  [| (problem_49_pre n_pre p_pre ) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| (2 <= p_pre) |] 
  &&  [| ((p_pre * 2 ) <= INT_MAX) |]
  &&  emp
|--
  [| (problem_49_spec n_pre p_pre out ) |]
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_modp_safety_wit_1 : modp_safety_wit_1.
Axiom proof_of_modp_safety_wit_2 : modp_safety_wit_2.
Axiom proof_of_modp_safety_wit_3 : modp_safety_wit_3.
Axiom proof_of_modp_safety_wit_4 : modp_safety_wit_4.
Axiom proof_of_modp_safety_wit_5 : modp_safety_wit_5.
Axiom proof_of_modp_safety_wit_6 : modp_safety_wit_6.
Axiom proof_of_modp_entail_wit_1 : modp_entail_wit_1.
Axiom proof_of_modp_entail_wit_2 : modp_entail_wit_2.
Axiom proof_of_modp_return_wit_1 : modp_return_wit_1.

End VC_Correct.
