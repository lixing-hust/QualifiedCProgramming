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
Require Import coins_131.
Local Open Scope sac.
Require Import common_strategy_goal.
Require Import common_strategy_proof.

(*----- Function digits -----*)

Definition digits_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "has" ) )) # Int  |->_)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digits_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "prod" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition digits_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digits_safety_wit_4 := 
forall (n_pre: Z) ,
  [| (n_pre = 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| False |]
.

Definition digits_safety_wit_5 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digits_safety_wit_6 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| ((n <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition digits_safety_wit_7 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition digits_safety_wit_8 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (((n % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition digits_safety_wit_9 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition digits_safety_wit_10 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition digits_safety_wit_11 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (((n % ( 10 ) ) % ( 2 ) ) = 1) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition digits_safety_wit_12 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (((n % ( 10 ) ) % ( 2 ) ) = 1) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  [| ((prod * (n % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (prod * (n % ( 10 ) ) )) |]
.

Definition digits_safety_wit_13 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (((n % ( 10 ) ) % ( 2 ) ) <> 1) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| ((n <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition digits_safety_wit_14 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (((n % ( 10 ) ) % ( 2 ) ) <> 1) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition digits_safety_wit_15 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (((n % ( 10 ) ) % ( 2 ) ) = 1) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  [| ((n <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition digits_safety_wit_16 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (((n % ( 10 ) ) % ( 2 ) ) = 1) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition digits_safety_wit_17 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (n <= 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digits_safety_wit_18 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (has = 0) |] 
  &&  [| (n <= 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition digits_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| (n_pre >= 0) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (1 <= INT_MAX) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| ((1 * (raw_odd_prod_z (n_pre)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n_pre) (1) (0)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  emp
.

Definition digits_entail_wit_2_1 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (((n % ( 10 ) ) % ( 2 ) ) = 1) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| ((n ÷ 10 ) >= 0) |] 
  &&  [| (1 <= (prod * (n % ( 10 ) ) )) |] 
  &&  [| ((prod * (n % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (((prod * (n % ( 10 ) ) ) * (raw_odd_prod_z ((n ÷ 10 ))) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  emp
.

Definition digits_entail_wit_2_2 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (((n % ( 10 ) ) % ( 2 ) ) <> 1) |] 
  &&  [| (n > 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| ((n ÷ 10 ) >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z ((n ÷ 10 ))) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z ((n ÷ 10 )) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  emp
.

Definition digits_return_wit_1 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (has = 0) |] 
  &&  [| (n <= 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| (problem_131_spec_z n_pre 0 ) |]
  &&  emp
.

Definition digits_return_wit_2 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) ,
  [| (has <> 0) |] 
  &&  [| (n <= 0) |] 
  &&  [| (n >= 0) |] 
  &&  [| (1 <= prod) |] 
  &&  [| (prod <= INT_MAX) |] 
  &&  [| (0 <= has) |] 
  &&  [| (has <= 1) |] 
  &&  [| ((prod * (raw_odd_prod_z (n)) ) <= INT_MAX) |] 
  &&  [| (problem_131_spec_z n_pre (digits_loop_z (n) (prod) (has)) ) |] 
  &&  [| (n_pre <> 0) |] 
  &&  [| (problem_131_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((raw_odd_prod_z (n_pre)) <= INT_MAX) |]
  &&  emp
|--
  [| (problem_131_spec_z n_pre prod ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_digits_safety_wit_1 : digits_safety_wit_1.
Axiom proof_of_digits_safety_wit_2 : digits_safety_wit_2.
Axiom proof_of_digits_safety_wit_3 : digits_safety_wit_3.
Axiom proof_of_digits_safety_wit_4 : digits_safety_wit_4.
Axiom proof_of_digits_safety_wit_5 : digits_safety_wit_5.
Axiom proof_of_digits_safety_wit_6 : digits_safety_wit_6.
Axiom proof_of_digits_safety_wit_7 : digits_safety_wit_7.
Axiom proof_of_digits_safety_wit_8 : digits_safety_wit_8.
Axiom proof_of_digits_safety_wit_9 : digits_safety_wit_9.
Axiom proof_of_digits_safety_wit_10 : digits_safety_wit_10.
Axiom proof_of_digits_safety_wit_11 : digits_safety_wit_11.
Axiom proof_of_digits_safety_wit_12 : digits_safety_wit_12.
Axiom proof_of_digits_safety_wit_13 : digits_safety_wit_13.
Axiom proof_of_digits_safety_wit_14 : digits_safety_wit_14.
Axiom proof_of_digits_safety_wit_15 : digits_safety_wit_15.
Axiom proof_of_digits_safety_wit_16 : digits_safety_wit_16.
Axiom proof_of_digits_safety_wit_17 : digits_safety_wit_17.
Axiom proof_of_digits_safety_wit_18 : digits_safety_wit_18.
Axiom proof_of_digits_entail_wit_1 : digits_entail_wit_1.
Axiom proof_of_digits_entail_wit_2_1 : digits_entail_wit_2_1.
Axiom proof_of_digits_entail_wit_2_2 : digits_entail_wit_2_2.
Axiom proof_of_digits_return_wit_1 : digits_return_wit_1.
Axiom proof_of_digits_return_wit_2 : digits_return_wit_2.

End VC_Correct.
