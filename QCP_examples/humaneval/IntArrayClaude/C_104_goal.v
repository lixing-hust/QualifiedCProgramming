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
Require Import coins_104.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function has_only_odd_digits_int -----*)

Definition has_only_odd_digits_int_safety_wit_1 := 
forall (value_pre: Z) ,
  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |]
  &&  ((( &( "u" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> value_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition has_only_odd_digits_int_safety_wit_2 := 
forall (value_pre: Z) ,
  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |]
  &&  ((( &( "u" ) )) # Int  |-> 1)
  **  ((( &( "num" ) )) # Int  |-> value_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition has_only_odd_digits_int_safety_wit_3 := 
forall (value_pre: Z) ,
  [| (value_pre = 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |]
  &&  ((( &( "u" ) )) # Int  |-> 1)
  **  ((( &( "num" ) )) # Int  |-> value_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  [| False |]
.

Definition has_only_odd_digits_int_safety_wit_4 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition has_only_odd_digits_int_safety_wit_5 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition has_only_odd_digits_int_safety_wit_6 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u = 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| False |]
.

Definition has_only_odd_digits_int_safety_wit_7 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| False |]
.

Definition has_only_odd_digits_int_safety_wit_8 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| ((num <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition has_only_odd_digits_int_safety_wit_9 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition has_only_odd_digits_int_safety_wit_10 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition has_only_odd_digits_int_safety_wit_11 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| ((num % ( 2 ) ) = 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition has_only_odd_digits_int_safety_wit_12 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| ((num % ( 2 ) ) <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| ((num <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition has_only_odd_digits_int_safety_wit_13 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| ((num % ( 2 ) ) <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> u)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition has_only_odd_digits_int_safety_wit_14 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| ((num % ( 2 ) ) = 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> 0)
|--
  [| ((num <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition has_only_odd_digits_int_safety_wit_15 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| ((num % ( 2 ) ) = 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "u" ) )) # Int  |-> 0)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition has_only_odd_digits_int_entail_wit_1 := 
forall (value_pre: Z) ,
  [| (value_pre <> 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |]
  &&  emp
|--
  ([| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= value_pre) |] 
  &&  [| (value_pre <= value_pre) |] 
  &&  [| (1 = 1) |] 
  &&  [| (odd_digit_scan_state value_pre value_pre 1 ) |]
  &&  emp)
  ||
  ([| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= value_pre) |] 
  &&  [| (value_pre <= value_pre) |] 
  &&  [| (1 = 0) |] 
  &&  [| (odd_digit_scan_state value_pre value_pre 1 ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_entail_wit_2_1 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u = 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (u = 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
  ||
  ([| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
  ||
  ([| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_entail_wit_2_2 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u = 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (u = 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
  ||
  ([| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
  ||
  ([| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_entail_wit_2_3 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (u = 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
  ||
  ([| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
  ||
  ([| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_entail_wit_2_4 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (u = 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
  ||
  ([| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
  ||
  ([| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_entail_wit_3_1 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
.

Definition has_only_odd_digits_int_entail_wit_3_2 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
.

Definition has_only_odd_digits_int_entail_wit_4_1 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| ((num % ( 2 ) ) = 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= (num ÷ 10 )) |] 
  &&  [| ((num ÷ 10 ) <= value_pre) |] 
  &&  [| (0 = 1) |] 
  &&  [| (odd_digit_scan_state value_pre (num ÷ 10 ) 0 ) |]
  &&  emp)
  ||
  ([| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= (num ÷ 10 )) |] 
  &&  [| ((num ÷ 10 ) <= value_pre) |] 
  &&  [| (0 = 0) |] 
  &&  [| (odd_digit_scan_state value_pre (num ÷ 10 ) 0 ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_entail_wit_4_2 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| ((num % ( 2 ) ) <> 0) |] 
  &&  [| (u <> 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= (num ÷ 10 )) |] 
  &&  [| ((num ÷ 10 ) <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre (num ÷ 10 ) u ) |]
  &&  emp)
  ||
  ([| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= (num ÷ 10 )) |] 
  &&  [| ((num ÷ 10 ) <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre (num ÷ 10 ) u ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_return_wit_1 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (u <> 0) |] 
  &&  [| (only_odd_digits_z value_pre ) |]
  &&  emp)
  ||
  ([| (u = 0) |] 
  &&  [| (has_even_digit_z value_pre ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_return_wit_2 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (num <= 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 1) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (u <> 0) |] 
  &&  [| (only_odd_digits_z value_pre ) |]
  &&  emp)
  ||
  ([| (u = 0) |] 
  &&  [| (has_even_digit_z value_pre ) |]
  &&  emp)
.

Definition has_only_odd_digits_int_return_wit_3 := 
forall (value_pre: Z) (u: Z) (num: Z) ,
  [| (u = 0) |] 
  &&  [| (num > 0) |] 
  &&  [| (0 < value_pre) |] 
  &&  [| (value_pre < INT_MAX) |] 
  &&  [| (0 <= num) |] 
  &&  [| (num <= value_pre) |] 
  &&  [| (u = 0) |] 
  &&  [| (odd_digit_scan_state value_pre num u ) |]
  &&  emp
|--
  ([| (u <> 0) |] 
  &&  [| (only_odd_digits_z value_pre ) |]
  &&  emp)
  ||
  ([| (u = 0) |] 
  &&  [| (has_even_digit_z value_pre ) |]
  &&  emp)
.

(*----- Function unique_digits -----*)

Definition unique_digits_safety_wit_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition unique_digits_safety_wit_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 x_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition unique_digits_safety_wit_3 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 x_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition unique_digits_safety_wit_4 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval = 0) |]
  &&  ((( &( "u" ) )) # Int  |-> retval)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| False |]
.

Definition unique_digits_safety_wit_5 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (has_even_digit_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  ((( &( "u" ) )) # Int  |-> retval)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| False |]
.

Definition unique_digits_safety_wit_6 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  ((( &( "u" ) )) # Int  |-> retval)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition unique_digits_safety_wit_7 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  ((( &( "u" ) )) # Int  |-> retval)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition unique_digits_safety_wit_8 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (has_even_digit_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition unique_digits_safety_wit_9 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition unique_digits_safety_wit_10 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l x_size_pre output_l ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> x_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition unique_digits_entail_wit_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  (IntArray.undef_full retval_2 x_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  EX (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l 0 output_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 x_size_pre )
.

Definition unique_digits_entail_wit_2_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (retval = 0) |] 
  &&  [| (has_even_digit_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_2_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (has_even_digit_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (retval = 0) |] 
  &&  [| (has_even_digit_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_3_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_3_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (has_even_digit_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_4_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (unique_digits_prefix input_l i output_l_2 ) |] 
  &&  [| (retval <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= x_size_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) <= (i + 1 )) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l (i + 1 ) output_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
.

Definition unique_digits_entail_wit_4_2 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (has_even_digit_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (unique_digits_prefix input_l i output_l_2 ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l (i + 1 ) output_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_5 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (unique_digits_prefix input_l i output_l_2 ) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l x_size_pre output_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> x_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_entail_wit_6 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (output_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) ,
  [| (output_size = (Zlength (sorted_l_2))) |] 
  &&  [| (x_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| ((sublist (0) (output_size) (sorted_full_l)) = sorted_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation output_l_2 sorted_l_2 ) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (unique_digits_prefix input_l x_size_pre output_l_2 ) |]
  &&  (IntArray.full data x_size_pre sorted_full_l )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (data_l: (@list Z))  (sorted_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size = (Zlength (sorted_l))) |] 
  &&  [| (x_size_pre = (Zlength (data_l))) |] 
  &&  [| ((sublist (0) (output_size) (data_l)) = sorted_l) |] 
  &&  [| (unique_digits_prefix input_l x_size_pre output_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation output_l sorted_l ) |] 
  &&  [| (problem_104_spec_z input_l sorted_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full data x_size_pre data_l )
.

Definition unique_digits_return_wit_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) ,
  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= x_size_pre) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_size_2 = (Zlength (sorted_l))) |] 
  &&  [| (x_size_pre = (Zlength (data_l_2))) |] 
  &&  [| ((sublist (0) (output_size_2) (data_l_2)) = sorted_l) |] 
  &&  [| (unique_digits_prefix input_l x_size_pre output_l_2 ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation output_l_2 sorted_l ) |] 
  &&  [| (problem_104_spec_z input_l sorted_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.full data_2 x_size_pre data_l_2 )
|--
  EX (data_l: (@list Z))  (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (x_size_pre = (Zlength (data_l))) |] 
  &&  [| ((sublist (0) (output_size) (data_l)) = output_l) |] 
  &&  [| (problem_104_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data x_size_pre data_l )
  **  (IntArray.full x_pre x_size_pre input_l )
.

Definition unique_digits_partial_solve_wit_1 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
|--
  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
.

Definition unique_digits_partial_solve_wit_2_pure := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  [| (x_size_pre >= 0) |] 
  &&  [| (x_size_pre < INT_MAX) |]
.

Definition unique_digits_partial_solve_wit_2_aux := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full x_pre x_size_pre input_l )
|--
  [| (x_size_pre >= 0) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full x_pre x_size_pre input_l )
.

Definition unique_digits_partial_solve_wit_2 := unique_digits_partial_solve_wit_2_pure -> unique_digits_partial_solve_wit_2_aux.

Definition unique_digits_partial_solve_wit_3 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |]
  &&  (((x_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i x_pre i 0 x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_partial_solve_wit_4_pure := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |]
  &&  ((( &( "u" ) )) # Int  |->_)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| ((Znth i input_l 0) < INT_MAX) |] 
  &&  [| (0 < (Znth i input_l 0)) |]
.

Definition unique_digits_partial_solve_wit_4_aux := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| ((Znth i input_l 0) < INT_MAX) |] 
  &&  [| (0 < (Znth i input_l 0)) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
.

Definition unique_digits_partial_solve_wit_4 := unique_digits_partial_solve_wit_4_pure -> unique_digits_partial_solve_wit_4_aux.

Definition unique_digits_partial_solve_wit_5 := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (retval <> 0) |] 
  &&  [| (only_odd_digits_z (Znth i input_l 0) ) |] 
  &&  [| (i < x_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= x_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l i output_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) x_size_pre )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition unique_digits_partial_solve_wit_6_pure := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l x_size_pre output_l ) |]
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "x_size" ) )) # Int  |-> x_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> x_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (data <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |]
.

Definition unique_digits_partial_solve_wit_6_aux := 
forall (x_size_pre: Z) (x_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l x_size_pre output_l ) |]
  &&  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
|--
  [| (data <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= x_size_pre) |] 
  &&  [| (x_size_pre < INT_MAX) |] 
  &&  [| (x_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_104_pre_z input_l ) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= x_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (unique_digits_prefix input_l x_size_pre output_l ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size x_size_pre )
  **  (IntArray.full x_pre x_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition unique_digits_partial_solve_wit_6 := unique_digits_partial_solve_wit_6_pure -> unique_digits_partial_solve_wit_6_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_has_only_odd_digits_int_safety_wit_1 : has_only_odd_digits_int_safety_wit_1.
Axiom proof_of_has_only_odd_digits_int_safety_wit_2 : has_only_odd_digits_int_safety_wit_2.
Axiom proof_of_has_only_odd_digits_int_safety_wit_3 : has_only_odd_digits_int_safety_wit_3.
Axiom proof_of_has_only_odd_digits_int_safety_wit_4 : has_only_odd_digits_int_safety_wit_4.
Axiom proof_of_has_only_odd_digits_int_safety_wit_5 : has_only_odd_digits_int_safety_wit_5.
Axiom proof_of_has_only_odd_digits_int_safety_wit_6 : has_only_odd_digits_int_safety_wit_6.
Axiom proof_of_has_only_odd_digits_int_safety_wit_7 : has_only_odd_digits_int_safety_wit_7.
Axiom proof_of_has_only_odd_digits_int_safety_wit_8 : has_only_odd_digits_int_safety_wit_8.
Axiom proof_of_has_only_odd_digits_int_safety_wit_9 : has_only_odd_digits_int_safety_wit_9.
Axiom proof_of_has_only_odd_digits_int_safety_wit_10 : has_only_odd_digits_int_safety_wit_10.
Axiom proof_of_has_only_odd_digits_int_safety_wit_11 : has_only_odd_digits_int_safety_wit_11.
Axiom proof_of_has_only_odd_digits_int_safety_wit_12 : has_only_odd_digits_int_safety_wit_12.
Axiom proof_of_has_only_odd_digits_int_safety_wit_13 : has_only_odd_digits_int_safety_wit_13.
Axiom proof_of_has_only_odd_digits_int_safety_wit_14 : has_only_odd_digits_int_safety_wit_14.
Axiom proof_of_has_only_odd_digits_int_safety_wit_15 : has_only_odd_digits_int_safety_wit_15.
Axiom proof_of_has_only_odd_digits_int_entail_wit_1 : has_only_odd_digits_int_entail_wit_1.
Axiom proof_of_has_only_odd_digits_int_entail_wit_2_1 : has_only_odd_digits_int_entail_wit_2_1.
Axiom proof_of_has_only_odd_digits_int_entail_wit_2_2 : has_only_odd_digits_int_entail_wit_2_2.
Axiom proof_of_has_only_odd_digits_int_entail_wit_2_3 : has_only_odd_digits_int_entail_wit_2_3.
Axiom proof_of_has_only_odd_digits_int_entail_wit_2_4 : has_only_odd_digits_int_entail_wit_2_4.
Axiom proof_of_has_only_odd_digits_int_entail_wit_3_1 : has_only_odd_digits_int_entail_wit_3_1.
Axiom proof_of_has_only_odd_digits_int_entail_wit_3_2 : has_only_odd_digits_int_entail_wit_3_2.
Axiom proof_of_has_only_odd_digits_int_entail_wit_4_1 : has_only_odd_digits_int_entail_wit_4_1.
Axiom proof_of_has_only_odd_digits_int_entail_wit_4_2 : has_only_odd_digits_int_entail_wit_4_2.
Axiom proof_of_has_only_odd_digits_int_return_wit_1 : has_only_odd_digits_int_return_wit_1.
Axiom proof_of_has_only_odd_digits_int_return_wit_2 : has_only_odd_digits_int_return_wit_2.
Axiom proof_of_has_only_odd_digits_int_return_wit_3 : has_only_odd_digits_int_return_wit_3.
Axiom proof_of_unique_digits_safety_wit_1 : unique_digits_safety_wit_1.
Axiom proof_of_unique_digits_safety_wit_2 : unique_digits_safety_wit_2.
Axiom proof_of_unique_digits_safety_wit_3 : unique_digits_safety_wit_3.
Axiom proof_of_unique_digits_safety_wit_4 : unique_digits_safety_wit_4.
Axiom proof_of_unique_digits_safety_wit_5 : unique_digits_safety_wit_5.
Axiom proof_of_unique_digits_safety_wit_6 : unique_digits_safety_wit_6.
Axiom proof_of_unique_digits_safety_wit_7 : unique_digits_safety_wit_7.
Axiom proof_of_unique_digits_safety_wit_8 : unique_digits_safety_wit_8.
Axiom proof_of_unique_digits_safety_wit_9 : unique_digits_safety_wit_9.
Axiom proof_of_unique_digits_safety_wit_10 : unique_digits_safety_wit_10.
Axiom proof_of_unique_digits_entail_wit_1 : unique_digits_entail_wit_1.
Axiom proof_of_unique_digits_entail_wit_2_1 : unique_digits_entail_wit_2_1.
Axiom proof_of_unique_digits_entail_wit_2_2 : unique_digits_entail_wit_2_2.
Axiom proof_of_unique_digits_entail_wit_3_1 : unique_digits_entail_wit_3_1.
Axiom proof_of_unique_digits_entail_wit_3_2 : unique_digits_entail_wit_3_2.
Axiom proof_of_unique_digits_entail_wit_4_1 : unique_digits_entail_wit_4_1.
Axiom proof_of_unique_digits_entail_wit_4_2 : unique_digits_entail_wit_4_2.
Axiom proof_of_unique_digits_entail_wit_5 : unique_digits_entail_wit_5.
Axiom proof_of_unique_digits_entail_wit_6 : unique_digits_entail_wit_6.
Axiom proof_of_unique_digits_return_wit_1 : unique_digits_return_wit_1.
Axiom proof_of_unique_digits_partial_solve_wit_1 : unique_digits_partial_solve_wit_1.
Axiom proof_of_unique_digits_partial_solve_wit_2_pure : unique_digits_partial_solve_wit_2_pure.
Axiom proof_of_unique_digits_partial_solve_wit_2 : unique_digits_partial_solve_wit_2.
Axiom proof_of_unique_digits_partial_solve_wit_3 : unique_digits_partial_solve_wit_3.
Axiom proof_of_unique_digits_partial_solve_wit_4_pure : unique_digits_partial_solve_wit_4_pure.
Axiom proof_of_unique_digits_partial_solve_wit_4 : unique_digits_partial_solve_wit_4.
Axiom proof_of_unique_digits_partial_solve_wit_5 : unique_digits_partial_solve_wit_5.
Axiom proof_of_unique_digits_partial_solve_wit_6_pure : unique_digits_partial_solve_wit_6_pure.
Axiom proof_of_unique_digits_partial_solve_wit_6 : unique_digits_partial_solve_wit_6.

End VC_Correct.
