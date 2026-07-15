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
Require Import coins_36.
Local Open Scope sac.

(*----- Function fizz_buzz -----*)

Definition fizz_buzz_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_36_pre_z n_pre )) (PreH4 : (fizz_buzz_prefix_safe_z n_pre )) (PreH5 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_36_pre_z n_pre )) (PreH4 : (fizz_buzz_prefix_safe_z n_pre )) (PreH5 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_3 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (count = (fizz_buzz_prefix_z (i)))) (PreH10 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i <> (INT_MIN)) \/ (11 <> (-1))) ” 
  &&  “ (11 <> 0) ”
.

Definition fizz_buzz_safety_wit_4 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (count = (fizz_buzz_prefix_z (i)))) (PreH10 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (11 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 11) ”
.

Definition fizz_buzz_safety_wit_5 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (count = (fizz_buzz_prefix_z (i)))) (PreH10 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_6 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i <> (INT_MIN)) \/ (13 <> (-1))) ” 
  &&  “ (13 <> 0) ”
.

Definition fizz_buzz_safety_wit_7 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (13 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 13) ”
.

Definition fizz_buzz_safety_wit_8 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) <> 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_9 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  ((( &( "digit_count" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_10 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  ((( &( "digit_count" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_11 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_36_pre_z n_pre )) (PreH4 : (fizz_buzz_prefix_safe_z n_pre )) (PreH5 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (divisible_11_or_13_z i )) (PreH9 : (0 <= q)) (PreH10 : (q <= i)) (PreH11 : (0 <= digit_count)) (PreH12 : (digit_count <= (count_digit7_z (i)))) (PreH13 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH14 : (digit7_state_z i q digit_count )) (PreH15 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH16 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH17 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition fizz_buzz_safety_wit_12 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : (q > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (divisible_11_or_13_z i )) (PreH10 : (0 <= q)) (PreH11 : (q <= i)) (PreH12 : (0 <= digit_count)) (PreH13 : (digit_count <= (count_digit7_z (i)))) (PreH14 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH15 : (digit7_state_z i q digit_count )) (PreH16 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH17 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_13 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : (q > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (divisible_11_or_13_z i )) (PreH10 : (0 <= q)) (PreH11 : (q <= i)) (PreH12 : (0 <= digit_count)) (PreH13 : (digit_count <= (count_digit7_z (i)))) (PreH14 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH15 : (digit7_state_z i q digit_count )) (PreH16 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH17 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_14 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : (q > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (divisible_11_or_13_z i )) (PreH10 : (0 <= q)) (PreH11 : (q <= i)) (PreH12 : (0 <= digit_count)) (PreH13 : (digit_count <= (count_digit7_z (i)))) (PreH14 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH15 : (digit7_state_z i q digit_count )) (PreH16 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH17 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition fizz_buzz_safety_wit_15 := 
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
) \/
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
).

Definition fizz_buzz_safety_wit_15_split_goal_1 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ”
.

Definition fizz_buzz_safety_wit_15_split_goal_2 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition fizz_buzz_safety_wit_16 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fizz_buzz_safety_wit_17 := 
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((digit_count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit_count + 1 )) ”
) \/
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((digit_count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digit_count + 1 )) ”
).

Definition fizz_buzz_safety_wit_17_split_goal_1 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((digit_count + 1 ) <= INT_MAX) ”
.

Definition fizz_buzz_safety_wit_17_split_goal_2 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((INT_MIN) <= (digit_count + 1 )) ”
.

Definition fizz_buzz_safety_wit_18 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition fizz_buzz_safety_wit_19 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> (digit_count + 1 ))
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_20 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> (digit_count + 1 ))
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_21 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((q <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition fizz_buzz_safety_wit_22 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "digit_count" ) )) # Int  |-> digit_count)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition fizz_buzz_safety_wit_23 := 
forall (n_pre: Z) (i: Z) (count: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_36_pre_z n_pre )) (PreH4 : (fizz_buzz_prefix_safe_z n_pre )) (PreH5 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (count = (fizz_buzz_prefix_z ((i + 1 ))))) (PreH9 : (count <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition fizz_buzz_entail_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_36_pre_z n_pre )) (PreH4 : (fizz_buzz_prefix_safe_z n_pre )) (PreH5 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_36_pre_z n_pre ) ” 
  &&  “ (fizz_buzz_prefix_safe_z n_pre ) ” 
  &&  “ ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (fizz_buzz_prefix_z (0))) ” 
  &&  “ (0 <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_36_pre_z n_pre )) (PreH4 : (fizz_buzz_prefix_safe_z n_pre )) (PreH5 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (fizz_buzz_prefix_z (0))) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_36_pre_z n_pre )) (PreH4 : (fizz_buzz_prefix_safe_z n_pre )) (PreH5 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (fizz_buzz_prefix_z (0))) ”
.

Definition fizz_buzz_entail_wit_2_1 := 
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_36_pre_z n_pre ) ” 
  &&  “ (fizz_buzz_prefix_safe_z n_pre ) ” 
  &&  “ ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (divisible_11_or_13_z i ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (count_digit7_z (i))) ” 
  &&  “ (count = ((fizz_buzz_prefix_z (i)) + 0 )) ” 
  &&  “ (digit7_state_z i i 0 ) ” 
  &&  “ ((count + (count_digit7_z (i)) ) <= INT_MAX) ” 
  &&  “ ((0 + (count_digit7_z (i)) ) <= INT_MAX) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 + (count_digit7_z (i)) ) <= INT_MAX) ” 
  &&  “ ((count + (count_digit7_z (i)) ) <= INT_MAX) ” 
  &&  “ (digit7_state_z i i 0 ) ” 
  &&  “ (0 <= (count_digit7_z (i))) ” 
  &&  “ (divisible_11_or_13_z i ) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 + (count_digit7_z (i)) ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((count + (count_digit7_z (i)) ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_2_1_split_goal_3 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (digit7_state_z i i 0 ) ”
.

Definition fizz_buzz_entail_wit_2_1_split_goal_4 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (count_digit7_z (i))) ”
.

Definition fizz_buzz_entail_wit_2_1_split_goal_5 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 11 ) ) = 0)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (count = (fizz_buzz_prefix_z (i)))) (PreH11 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (divisible_11_or_13_z i ) ”
.

Definition fizz_buzz_entail_wit_2_2 := 
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_36_pre_z n_pre ) ” 
  &&  “ (fizz_buzz_prefix_safe_z n_pre ) ” 
  &&  “ ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (divisible_11_or_13_z i ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (count_digit7_z (i))) ” 
  &&  “ (count = ((fizz_buzz_prefix_z (i)) + 0 )) ” 
  &&  “ (digit7_state_z i i 0 ) ” 
  &&  “ ((count + (count_digit7_z (i)) ) <= INT_MAX) ” 
  &&  “ ((0 + (count_digit7_z (i)) ) <= INT_MAX) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 + (count_digit7_z (i)) ) <= INT_MAX) ” 
  &&  “ ((count + (count_digit7_z (i)) ) <= INT_MAX) ” 
  &&  “ (digit7_state_z i i 0 ) ” 
  &&  “ (0 <= (count_digit7_z (i))) ” 
  &&  “ (divisible_11_or_13_z i ) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((0 + (count_digit7_z (i)) ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((count + (count_digit7_z (i)) ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_2_2_split_goal_3 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (digit7_state_z i i 0 ) ”
.

Definition fizz_buzz_entail_wit_2_2_split_goal_4 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (count_digit7_z (i))) ”
.

Definition fizz_buzz_entail_wit_2_2_split_goal_5 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) = 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (divisible_11_or_13_z i ) ”
.

Definition fizz_buzz_entail_wit_3_1 := 
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_36_pre_z n_pre ) ” 
  &&  “ (fizz_buzz_prefix_safe_z n_pre ) ” 
  &&  “ ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (divisible_11_or_13_z i ) ” 
  &&  “ (0 <= (q ÷ 10 )) ” 
  &&  “ ((q ÷ 10 ) <= i) ” 
  &&  “ (0 <= (digit_count + 1 )) ” 
  &&  “ ((digit_count + 1 ) <= (count_digit7_z (i))) ” 
  &&  “ ((count + 1 ) = ((fizz_buzz_prefix_z (i)) + (digit_count + 1 ) )) ” 
  &&  “ (digit7_state_z i (q ÷ 10 ) (digit_count + 1 ) ) ” 
  &&  “ (((count + 1 ) + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ” 
  &&  “ (((digit_count + 1 ) + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ” 
  &&  “ ((count + 1 ) <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ (((digit_count + 1 ) + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ” 
  &&  “ (((count + 1 ) + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ” 
  &&  “ (digit7_state_z i (q ÷ 10 ) (digit_count + 1 ) ) ” 
  &&  “ ((digit_count + 1 ) <= (count_digit7_z (i))) ” 
  &&  “ ((q ÷ 10 ) <= i) ” 
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((count + 1 ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_3_1_split_goal_2 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (((digit_count + 1 ) + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_3_1_split_goal_3 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (((count + 1 ) + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_3_1_split_goal_4 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (digit7_state_z i (q ÷ 10 ) (digit_count + 1 ) ) ”
.

Definition fizz_buzz_entail_wit_3_1_split_goal_5 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((digit_count + 1 ) <= (count_digit7_z (i))) ”
.

Definition fizz_buzz_entail_wit_3_1_split_goal_6 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((q ÷ 10 ) <= i) ”
.

Definition fizz_buzz_entail_wit_3_1_split_goal_7 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) = 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (q ÷ 10 )) ”
.

Definition fizz_buzz_entail_wit_3_2 := 
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_36_pre_z n_pre ) ” 
  &&  “ (fizz_buzz_prefix_safe_z n_pre ) ” 
  &&  “ ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (divisible_11_or_13_z i ) ” 
  &&  “ (0 <= (q ÷ 10 )) ” 
  &&  “ ((q ÷ 10 ) <= i) ” 
  &&  “ (0 <= digit_count) ” 
  &&  “ (digit_count <= (count_digit7_z (i))) ” 
  &&  “ (count = ((fizz_buzz_prefix_z (i)) + digit_count )) ” 
  &&  “ (digit7_state_z i (q ÷ 10 ) digit_count ) ” 
  &&  “ ((count + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ” 
  &&  “ ((digit_count + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((digit_count + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ” 
  &&  “ ((count + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ” 
  &&  “ (digit7_state_z i (q ÷ 10 ) digit_count ) ” 
  &&  “ ((q ÷ 10 ) <= i) ” 
  &&  “ (0 <= (q ÷ 10 )) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((digit_count + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_3_2_split_goal_2 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((count + (count_digit7_z ((q ÷ 10 ))) ) <= INT_MAX) ”
.

Definition fizz_buzz_entail_wit_3_2_split_goal_3 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (digit7_state_z i (q ÷ 10 ) digit_count ) ”
.

Definition fizz_buzz_entail_wit_3_2_split_goal_4 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ ((q ÷ 10 ) <= i) ”
.

Definition fizz_buzz_entail_wit_3_2_split_goal_5 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : ((q % ( 10 ) ) <> 7)) (PreH2 : (q > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_36_pre_z n_pre )) (PreH6 : (fizz_buzz_prefix_safe_z n_pre )) (PreH7 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (divisible_11_or_13_z i )) (PreH11 : (0 <= q)) (PreH12 : (q <= i)) (PreH13 : (0 <= digit_count)) (PreH14 : (digit_count <= (count_digit7_z (i)))) (PreH15 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH16 : (digit7_state_z i q digit_count )) (PreH17 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH19 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= (q ÷ 10 )) ”
.

Definition fizz_buzz_entail_wit_4_1 := 
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) <> 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_36_pre_z n_pre ) ” 
  &&  “ (fizz_buzz_prefix_safe_z n_pre ) ” 
  &&  “ ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (count = (fizz_buzz_prefix_z ((i + 1 )))) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) <> 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (fizz_buzz_prefix_z ((i + 1 )))) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : ((i % ( 13 ) ) <> 0)) (PreH2 : ((i % ( 11 ) ) <> 0)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_36_pre_z n_pre )) (PreH7 : (fizz_buzz_prefix_safe_z n_pre )) (PreH8 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (count = (fizz_buzz_prefix_z (i)))) (PreH12 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (fizz_buzz_prefix_z ((i + 1 )))) ”
.

Definition fizz_buzz_entail_wit_4_2 := 
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (divisible_11_or_13_z i )) (PreH10 : (0 <= q)) (PreH11 : (q <= i)) (PreH12 : (0 <= digit_count)) (PreH13 : (digit_count <= (count_digit7_z (i)))) (PreH14 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH15 : (digit7_state_z i q digit_count )) (PreH16 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH17 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_36_pre_z n_pre ) ” 
  &&  “ (fizz_buzz_prefix_safe_z n_pre ) ” 
  &&  “ ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (count = (fizz_buzz_prefix_z ((i + 1 )))) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (divisible_11_or_13_z i )) (PreH10 : (0 <= q)) (PreH11 : (q <= i)) (PreH12 : (0 <= digit_count)) (PreH13 : (digit_count <= (count_digit7_z (i)))) (PreH14 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH15 : (digit7_state_z i q digit_count )) (PreH16 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH17 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (fizz_buzz_prefix_z ((i + 1 )))) ”
  &&  emp
).

Definition fizz_buzz_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (count: Z) (digit_count: Z) (q: Z) (i: Z) (PreH1 : (q <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (divisible_11_or_13_z i )) (PreH10 : (0 <= q)) (PreH11 : (q <= i)) (PreH12 : (0 <= digit_count)) (PreH13 : (digit_count <= (count_digit7_z (i)))) (PreH14 : (count = ((fizz_buzz_prefix_z (i)) + digit_count ))) (PreH15 : (digit7_state_z i q digit_count )) (PreH16 : ((count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH17 : ((digit_count + (count_digit7_z (q)) ) <= INT_MAX)) (PreH18 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (count = (fizz_buzz_prefix_z ((i + 1 )))) ”
.

Definition fizz_buzz_entail_wit_5 := 
forall (n_pre: Z) (i: Z) (count: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < INT_MAX)) (PreH3 : (problem_36_pre_z n_pre )) (PreH4 : (fizz_buzz_prefix_safe_z n_pre )) (PreH5 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (count = (fizz_buzz_prefix_z ((i + 1 ))))) (PreH9 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_36_pre_z n_pre ) ” 
  &&  “ (fizz_buzz_prefix_safe_z n_pre ) ” 
  &&  “ ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (count = (fizz_buzz_prefix_z ((i + 1 )))) ” 
  &&  “ (count <= INT_MAX) ”
  &&  emp
.

Definition fizz_buzz_return_wit_1 := 
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (count = (fizz_buzz_prefix_z (i)))) (PreH10 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_36_spec_z n_pre count ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (count = (fizz_buzz_prefix_z (i)))) (PreH10 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_36_spec_z n_pre count ) ”
  &&  emp
).

Definition fizz_buzz_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (count: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_36_pre_z n_pre )) (PreH5 : (fizz_buzz_prefix_safe_z n_pre )) (PreH6 : ((fizz_buzz_prefix_z (n_pre)) <= INT_MAX)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (count = (fizz_buzz_prefix_z (i)))) (PreH10 : (count <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_36_spec_z n_pre count ) ”
.

Module Type VC_Correct.


Axiom proof_of_fizz_buzz_safety_wit_1 : fizz_buzz_safety_wit_1.
Axiom proof_of_fizz_buzz_safety_wit_2 : fizz_buzz_safety_wit_2.
Axiom proof_of_fizz_buzz_safety_wit_3 : fizz_buzz_safety_wit_3.
Axiom proof_of_fizz_buzz_safety_wit_4 : fizz_buzz_safety_wit_4.
Axiom proof_of_fizz_buzz_safety_wit_5 : fizz_buzz_safety_wit_5.
Axiom proof_of_fizz_buzz_safety_wit_6 : fizz_buzz_safety_wit_6.
Axiom proof_of_fizz_buzz_safety_wit_7 : fizz_buzz_safety_wit_7.
Axiom proof_of_fizz_buzz_safety_wit_8 : fizz_buzz_safety_wit_8.
Axiom proof_of_fizz_buzz_safety_wit_9 : fizz_buzz_safety_wit_9.
Axiom proof_of_fizz_buzz_safety_wit_10 : fizz_buzz_safety_wit_10.
Axiom proof_of_fizz_buzz_safety_wit_11 : fizz_buzz_safety_wit_11.
Axiom proof_of_fizz_buzz_safety_wit_12 : fizz_buzz_safety_wit_12.
Axiom proof_of_fizz_buzz_safety_wit_13 : fizz_buzz_safety_wit_13.
Axiom proof_of_fizz_buzz_safety_wit_14 : fizz_buzz_safety_wit_14.
Axiom proof_of_fizz_buzz_safety_wit_15 : fizz_buzz_safety_wit_15.
Axiom proof_of_fizz_buzz_safety_wit_16 : fizz_buzz_safety_wit_16.
Axiom proof_of_fizz_buzz_safety_wit_17 : fizz_buzz_safety_wit_17.
Axiom proof_of_fizz_buzz_safety_wit_18 : fizz_buzz_safety_wit_18.
Axiom proof_of_fizz_buzz_safety_wit_19 : fizz_buzz_safety_wit_19.
Axiom proof_of_fizz_buzz_safety_wit_20 : fizz_buzz_safety_wit_20.
Axiom proof_of_fizz_buzz_safety_wit_21 : fizz_buzz_safety_wit_21.
Axiom proof_of_fizz_buzz_safety_wit_22 : fizz_buzz_safety_wit_22.
Axiom proof_of_fizz_buzz_safety_wit_23 : fizz_buzz_safety_wit_23.
Axiom proof_of_fizz_buzz_entail_wit_1 : fizz_buzz_entail_wit_1.
Axiom proof_of_fizz_buzz_entail_wit_2_1 : fizz_buzz_entail_wit_2_1.
Axiom proof_of_fizz_buzz_entail_wit_2_2 : fizz_buzz_entail_wit_2_2.
Axiom proof_of_fizz_buzz_entail_wit_3_1 : fizz_buzz_entail_wit_3_1.
Axiom proof_of_fizz_buzz_entail_wit_3_2 : fizz_buzz_entail_wit_3_2.
Axiom proof_of_fizz_buzz_entail_wit_4_1 : fizz_buzz_entail_wit_4_1.
Axiom proof_of_fizz_buzz_entail_wit_4_2 : fizz_buzz_entail_wit_4_2.
Axiom proof_of_fizz_buzz_entail_wit_5 : fizz_buzz_entail_wit_5.
Axiom proof_of_fizz_buzz_return_wit_1 : fizz_buzz_return_wit_1.

End VC_Correct.
