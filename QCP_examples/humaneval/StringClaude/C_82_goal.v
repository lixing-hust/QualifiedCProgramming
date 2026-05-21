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
Require Import coins_82.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function prime_length -----*)

Definition prime_length_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition prime_length_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval < 2) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prime_length_safety_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval >= 2) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition prime_length_safety_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i * i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * i )) |]
.

Definition prime_length_safety_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((i * i ) <= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((len <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition prime_length_safety_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((i * i ) <= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prime_length_safety_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((len % ( i ) ) = 0) |] 
  &&  [| ((i * i ) <= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition prime_length_safety_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((len % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition prime_length_safety_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((i * i ) > len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition prime_length_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval >= 2) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= 46340) |] 
  &&  [| (prime_prefix_z 2 len ) |]
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition prime_length_entail_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((len % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= 46340) |] 
  &&  [| (prime_prefix_z (i + 1 ) len ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition prime_length_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((i * i ) > len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_82_spec_z l 1 ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition prime_length_return_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  [| ((len % ( i ) ) = 0) |] 
  &&  [| ((i * i ) <= len) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |] 
  &&  [| (2 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i len ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_82_spec_z l 0 ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition prime_length_return_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  [| (retval < 2) |] 
  &&  [| (retval = len) |] 
  &&  [| (0 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (problem_82_spec_z l 0 ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition prime_length_partial_solve_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  [| (0 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  [| (0 <= len) |] 
  &&  [| (len <= 2147302921) |] 
  &&  [| ((Zlength (l)) = len) |] 
  &&  [| (problem_82_pre_z l ) |]
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_prime_length_safety_wit_1 : prime_length_safety_wit_1.
Axiom proof_of_prime_length_safety_wit_2 : prime_length_safety_wit_2.
Axiom proof_of_prime_length_safety_wit_3 : prime_length_safety_wit_3.
Axiom proof_of_prime_length_safety_wit_4 : prime_length_safety_wit_4.
Axiom proof_of_prime_length_safety_wit_5 : prime_length_safety_wit_5.
Axiom proof_of_prime_length_safety_wit_6 : prime_length_safety_wit_6.
Axiom proof_of_prime_length_safety_wit_7 : prime_length_safety_wit_7.
Axiom proof_of_prime_length_safety_wit_8 : prime_length_safety_wit_8.
Axiom proof_of_prime_length_safety_wit_9 : prime_length_safety_wit_9.
Axiom proof_of_prime_length_entail_wit_1 : prime_length_entail_wit_1.
Axiom proof_of_prime_length_entail_wit_2 : prime_length_entail_wit_2.
Axiom proof_of_prime_length_return_wit_1 : prime_length_return_wit_1.
Axiom proof_of_prime_length_return_wit_2 : prime_length_return_wit_2.
Axiom proof_of_prime_length_return_wit_3 : prime_length_return_wit_3.
Axiom proof_of_prime_length_partial_solve_wit_1 : prime_length_partial_solve_wit_1.

End VC_Correct.
