Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_131.
Local Open Scope sac.

(*----- Function digits -----*)

Definition digits_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_131_pre_z n_pre )) (PreH4 : (digits_product_safe_z n_pre )) ,
  ((( &( "has" ) )) # Int  |->_)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_131_pre_z n_pre )) (PreH4 : (digits_product_safe_z n_pre )) ,
  ((( &( "prod" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_131_pre_z n_pre )) (PreH4 : (digits_product_safe_z n_pre )) ,
  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_safety_wit_4 := 
forall (n_pre: Z) (PreH1 : (n_pre = 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) ,
  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ False ”
.

Definition digits_safety_wit_5 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_131_pre_z n_pre )) (PreH4 : (digits_product_safe_z n_pre )) (PreH5 : (0 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (0 <= prod)) (PreH8 : (prod <= INT_MAX)) (PreH9 : (has = 0)) (PreH10 : (digits_state_z n_pre n prod has )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_safety_wit_6 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (0 < n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_131_pre_z n_pre )) (PreH4 : (digits_product_safe_z n_pre )) (PreH5 : (0 <= n)) (PreH6 : (n <= n_pre)) (PreH7 : (0 <= prod)) (PreH8 : (prod <= INT_MAX)) (PreH9 : (has = 1)) (PreH10 : (digits_state_z n_pre n prod has )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_safety_wit_7 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 0)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition digits_safety_wit_8 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 0)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_safety_wit_9 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 1)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition digits_safety_wit_10 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 1)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_safety_wit_11 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 1)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (((n % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition digits_safety_wit_12 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 0)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (((n % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition digits_safety_wit_13 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 0)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition digits_safety_wit_14 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 1)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition digits_safety_wit_15 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 0)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_safety_wit_16 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n > 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 1)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_safety_wit_17 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_safety_wit_18 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digits_safety_wit_19 := 
(
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
) \/
(
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
).

Definition digits_safety_wit_19_split_goal_1 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ”
.

Definition digits_safety_wit_19_split_goal_2 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
.

Definition digits_safety_wit_20 := 
(
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
) \/
(
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
).

Definition digits_safety_wit_20_split_goal_1 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ”
.

Definition digits_safety_wit_20_split_goal_2 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
.

Definition digits_safety_wit_21 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition digits_safety_wit_22 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_safety_wit_23 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition digits_safety_wit_24 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_safety_wit_25 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition digits_safety_wit_26 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_safety_wit_27 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition digits_safety_wit_28 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digits_safety_wit_29 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 0)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_safety_wit_30 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (n <= 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) (PreH6 : (0 <= n)) (PreH7 : (n <= n_pre)) (PreH8 : (0 <= prod)) (PreH9 : (prod <= INT_MAX)) (PreH10 : (has = 1)) (PreH11 : (digits_state_z n_pre n prod has )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_safety_wit_31 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has <> 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ False ”
.

Definition digits_safety_wit_32 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has = 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ False ”
.

Definition digits_safety_wit_33 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has = 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "has" ) )) # Int  |-> has)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digits_entail_wit_1 := 
forall (n_pre: Z) (PreH1 : (n_pre <> 0)) (PreH2 : (0 < n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_131_pre_z n_pre )) (PreH5 : (digits_product_safe_z n_pre )) ,
  TT && emp 
|--
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (digits_state_z n_pre n_pre 1 0 ) ”
  &&  emp)
  ||
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= INT_MAX) ” 
  &&  “ (0 = 1) ” 
  &&  “ (digits_state_z n_pre n_pre 1 0 ) ”
  &&  emp)
.

Definition digits_entail_wit_2_1 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ (1 = 0) ” 
  &&  “ (digits_state_z n_pre (n ÷ 10 ) (prod * (n % ( 10 ) ) ) 1 ) ”
  &&  emp)
  ||
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ (1 = 1) ” 
  &&  “ (digits_state_z n_pre (n ÷ 10 ) (prod * (n % ( 10 ) ) ) 1 ) ”
  &&  emp)
.

Definition digits_entail_wit_2_2 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) = 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ (1 = 0) ” 
  &&  “ (digits_state_z n_pre (n ÷ 10 ) (prod * (n % ( 10 ) ) ) 1 ) ”
  &&  emp)
  ||
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ (1 = 1) ” 
  &&  “ (digits_state_z n_pre (n ÷ 10 ) (prod * (n % ( 10 ) ) ) 1 ) ”
  &&  emp)
.

Definition digits_entail_wit_2_3 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ (has = 0) ” 
  &&  “ (digits_state_z n_pre (n ÷ 10 ) prod has ) ”
  &&  emp)
  ||
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ (has = 1) ” 
  &&  “ (digits_state_z n_pre (n ÷ 10 ) prod has ) ”
  &&  emp)
.

Definition digits_entail_wit_2_4 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (((n % ( 10 ) ) % ( 2 ) ) <> 1)) (PreH2 : (n > 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ (has = 0) ” 
  &&  “ (digits_state_z n_pre (n ÷ 10 ) prod has ) ”
  &&  emp)
  ||
  (“ (0 < n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_131_pre_z n_pre ) ” 
  &&  “ (digits_product_safe_z n_pre ) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (prod <= INT_MAX) ” 
  &&  “ (has = 1) ” 
  &&  “ (digits_state_z n_pre (n ÷ 10 ) prod has ) ”
  &&  emp)
.

Definition digits_return_wit_1 := 
(
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has <> 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  “ (problem_131_spec_z n_pre prod ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has <> 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  “ (problem_131_spec_z n_pre prod ) ”
  &&  emp
).

Definition digits_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has <> 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 1)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  “ (problem_131_spec_z n_pre prod ) ”
.

Definition digits_return_wit_2 := 
(
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has = 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  “ (problem_131_spec_z n_pre 0 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has = 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  “ (problem_131_spec_z n_pre 0 ) ”
  &&  emp
).

Definition digits_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (has: Z) (prod: Z) (n: Z) (PreH1 : (has = 0)) (PreH2 : (n <= 0)) (PreH3 : (0 < n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_131_pre_z n_pre )) (PreH6 : (digits_product_safe_z n_pre )) (PreH7 : (0 <= n)) (PreH8 : (n <= n_pre)) (PreH9 : (0 <= prod)) (PreH10 : (prod <= INT_MAX)) (PreH11 : (has = 0)) (PreH12 : (digits_state_z n_pre n prod has )) ,
  TT && emp 
|--
  “ (problem_131_spec_z n_pre 0 ) ”
.

Module Type VC_Correct.


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
Axiom proof_of_digits_safety_wit_19 : digits_safety_wit_19.
Axiom proof_of_digits_safety_wit_20 : digits_safety_wit_20.
Axiom proof_of_digits_safety_wit_21 : digits_safety_wit_21.
Axiom proof_of_digits_safety_wit_22 : digits_safety_wit_22.
Axiom proof_of_digits_safety_wit_23 : digits_safety_wit_23.
Axiom proof_of_digits_safety_wit_24 : digits_safety_wit_24.
Axiom proof_of_digits_safety_wit_25 : digits_safety_wit_25.
Axiom proof_of_digits_safety_wit_26 : digits_safety_wit_26.
Axiom proof_of_digits_safety_wit_27 : digits_safety_wit_27.
Axiom proof_of_digits_safety_wit_28 : digits_safety_wit_28.
Axiom proof_of_digits_safety_wit_29 : digits_safety_wit_29.
Axiom proof_of_digits_safety_wit_30 : digits_safety_wit_30.
Axiom proof_of_digits_safety_wit_31 : digits_safety_wit_31.
Axiom proof_of_digits_safety_wit_32 : digits_safety_wit_32.
Axiom proof_of_digits_safety_wit_33 : digits_safety_wit_33.
Axiom proof_of_digits_entail_wit_1 : digits_entail_wit_1.
Axiom proof_of_digits_entail_wit_2_1 : digits_entail_wit_2_1.
Axiom proof_of_digits_entail_wit_2_2 : digits_entail_wit_2_2.
Axiom proof_of_digits_entail_wit_2_3 : digits_entail_wit_2_3.
Axiom proof_of_digits_entail_wit_2_4 : digits_entail_wit_2_4.
Axiom proof_of_digits_return_wit_1 : digits_return_wit_1.
Axiom proof_of_digits_return_wit_2 : digits_return_wit_2.

End VC_Correct.
