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
Require Import coins_39.
Local Open Scope sac.

(*----- Function prime_fib -----*)

Definition prime_fib_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) ,
  ((( &( "f2" ) )) # Int  |->_)
  **  ((( &( "f1" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prime_fib_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) ,
  ((( &( "f2" ) )) # Int  |->_)
  **  ((( &( "f1" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition prime_fib_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "f2" ) )) # Int  |-> 2)
  **  ((( &( "f1" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prime_fib_safety_wit_4 := 
(
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
|--
  “ ((f1 + f2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (f1 + f2 )) ”
) \/
(
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
|--
  “ ((f1 + f2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (f1 + f2 )) ”
).

Definition prime_fib_safety_wit_4_split_goal_1 := 
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
|--
  “ ((f1 + f2 ) <= INT_MAX) ”
.

Definition prime_fib_safety_wit_4_split_goal_2 := 
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
|--
  “ ((INT_MIN) <= (f1 + f2 )) ”
.

Definition prime_fib_safety_wit_5 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (f2 <= 144)) (PreH12 : (m = f2)) ,
  ((( &( "isprime" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prime_fib_safety_wit_6 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (f2 <= 144)) (PreH12 : (m = f2)) ,
  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "isprime" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition prime_fib_safety_wit_7 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 1)) (PreH15 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ ((f1 <> (INT_MIN)) \/ (w <> (-1))) ” 
  &&  “ (w <> 0) ”
.

Definition prime_fib_safety_wit_8 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 0)) (PreH15 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ ((f1 <> (INT_MIN)) \/ (w <> (-1))) ” 
  &&  “ (w <> 0) ”
.

Definition prime_fib_safety_wit_9 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w <= (f1 ÷ w ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count < n_pre)) (PreH9 : (pf_after_advance_z count f1 f2 )) (PreH10 : (2 <= f1)) (PreH11 : (f1 <= 89)) (PreH12 : (m = f2)) (PreH13 : (2 <= w)) (PreH14 : (w <= 10)) (PreH15 : (isprime = 1)) (PreH16 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition prime_fib_safety_wit_10 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w <= (f1 ÷ w ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count < n_pre)) (PreH9 : (pf_after_advance_z count f1 f2 )) (PreH10 : (2 <= f1)) (PreH11 : (f1 <= 89)) (PreH12 : (m = f2)) (PreH13 : (2 <= w)) (PreH14 : (w <= 10)) (PreH15 : (isprime = 0)) (PreH16 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition prime_fib_safety_wit_11 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w < 10)) (PreH2 : (w <= (f1 ÷ w ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_39_pre_z n_pre )) (PreH7 : (prime_fib_safe_z n_pre )) (PreH8 : (0 <= count)) (PreH9 : (count < n_pre)) (PreH10 : (pf_after_advance_z count f1 f2 )) (PreH11 : (2 <= f1)) (PreH12 : (f1 <= 89)) (PreH13 : (m = f2)) (PreH14 : (2 <= w)) (PreH15 : (w <= 10)) (PreH16 : (isprime = 1)) (PreH17 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ ((f1 <> (INT_MIN)) \/ (w <> (-1))) ” 
  &&  “ (w <> 0) ”
.

Definition prime_fib_safety_wit_12 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w < 10)) (PreH2 : (w <= (f1 ÷ w ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_39_pre_z n_pre )) (PreH7 : (prime_fib_safe_z n_pre )) (PreH8 : (0 <= count)) (PreH9 : (count < n_pre)) (PreH10 : (pf_after_advance_z count f1 f2 )) (PreH11 : (2 <= f1)) (PreH12 : (f1 <= 89)) (PreH13 : (m = f2)) (PreH14 : (2 <= w)) (PreH15 : (w <= 10)) (PreH16 : (isprime = 0)) (PreH17 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ ((f1 <> (INT_MIN)) \/ (w <> (-1))) ” 
  &&  “ (w <> 0) ”
.

Definition prime_fib_safety_wit_13 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w < 10)) (PreH2 : (w <= (f1 ÷ w ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_39_pre_z n_pre )) (PreH7 : (prime_fib_safe_z n_pre )) (PreH8 : (0 <= count)) (PreH9 : (count < n_pre)) (PreH10 : (pf_after_advance_z count f1 f2 )) (PreH11 : (2 <= f1)) (PreH12 : (f1 <= 89)) (PreH13 : (m = f2)) (PreH14 : (2 <= w)) (PreH15 : (w <= 10)) (PreH16 : (isprime = 0)) (PreH17 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prime_fib_safety_wit_14 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w < 10)) (PreH2 : (w <= (f1 ÷ w ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_39_pre_z n_pre )) (PreH7 : (prime_fib_safe_z n_pre )) (PreH8 : (0 <= count)) (PreH9 : (count < n_pre)) (PreH10 : (pf_after_advance_z count f1 f2 )) (PreH11 : (2 <= f1)) (PreH12 : (f1 <= 89)) (PreH13 : (m = f2)) (PreH14 : (2 <= w)) (PreH15 : (w <= 10)) (PreH16 : (isprime = 1)) (PreH17 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prime_fib_safety_wit_15 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : ((f1 % ( w ) ) = 0)) (PreH2 : (w < 10)) (PreH3 : (w <= (f1 ÷ w ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (problem_39_pre_z n_pre )) (PreH8 : (prime_fib_safe_z n_pre )) (PreH9 : (0 <= count)) (PreH10 : (count < n_pre)) (PreH11 : (pf_after_advance_z count f1 f2 )) (PreH12 : (2 <= f1)) (PreH13 : (f1 <= 89)) (PreH14 : (m = f2)) (PreH15 : (2 <= w)) (PreH16 : (w <= 10)) (PreH17 : (isprime = 0)) (PreH18 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prime_fib_safety_wit_16 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : ((f1 % ( w ) ) = 0)) (PreH2 : (w < 10)) (PreH3 : (w <= (f1 ÷ w ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (problem_39_pre_z n_pre )) (PreH8 : (prime_fib_safe_z n_pre )) (PreH9 : (0 <= count)) (PreH10 : (count < n_pre)) (PreH11 : (pf_after_advance_z count f1 f2 )) (PreH12 : (2 <= f1)) (PreH13 : (f1 <= 89)) (PreH14 : (m = f2)) (PreH15 : (2 <= w)) (PreH16 : (w <= 10)) (PreH17 : (isprime = 1)) (PreH18 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition prime_fib_safety_wit_17 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : ((f1 % ( w ) ) <> 0)) (PreH2 : (w < 10)) (PreH3 : (w <= (f1 ÷ w ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (problem_39_pre_z n_pre )) (PreH8 : (prime_fib_safe_z n_pre )) (PreH9 : (0 <= count)) (PreH10 : (count < n_pre)) (PreH11 : (pf_after_advance_z count f1 f2 )) (PreH12 : (2 <= f1)) (PreH13 : (f1 <= 89)) (PreH14 : (m = f2)) (PreH15 : (2 <= w)) (PreH16 : (w <= 10)) (PreH17 : (isprime = 0)) (PreH18 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ ((w + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (w + 1 )) ”
.

Definition prime_fib_safety_wit_18 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : ((f1 % ( w ) ) <> 0)) (PreH2 : (w < 10)) (PreH3 : (w <= (f1 ÷ w ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (problem_39_pre_z n_pre )) (PreH8 : (prime_fib_safe_z n_pre )) (PreH9 : (0 <= count)) (PreH10 : (count < n_pre)) (PreH11 : (pf_after_advance_z count f1 f2 )) (PreH12 : (2 <= f1)) (PreH13 : (f1 <= 89)) (PreH14 : (m = f2)) (PreH15 : (2 <= w)) (PreH16 : (w <= 10)) (PreH17 : (isprime = 1)) (PreH18 : (prime_scan_state_z f1 w isprime )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ ((w + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (w + 1 )) ”
.

Definition prime_fib_safety_wit_19 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 1)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ False ”
.

Definition prime_fib_safety_wit_20 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 0)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ False ”
.

Definition prime_fib_safety_wit_21 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 1)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition prime_fib_safety_wit_22 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 1)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime <> 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "f2" ) )) # Int  |-> f2)
  **  ((( &( "f1" ) )) # Int  |-> f1)
  **  ((( &( "m" ) )) # Int  |-> m)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "isprime" ) )) # Int  |-> isprime)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition prime_fib_entail_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (pf_loop_state_z 0 1 2 ) ” 
  &&  “ ((0 = n_pre) -> (finite_prime_candidate_z 1 )) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) ,
  TT && emp 
|--
  “ (pf_loop_state_z 0 1 2 ) ”
  &&  emp
).

Definition prime_fib_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) ,
  TT && emp 
|--
  “ (pf_loop_state_z 0 1 2 ) ”
.

Definition prime_fib_entail_wit_2 := 
(
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f2 (f1 + f2 ) ) ” 
  &&  “ (2 <= f2) ” 
  &&  “ (f2 <= 89) ” 
  &&  “ ((f1 + f2 ) <= 144) ” 
  &&  “ ((f1 + f2 ) = (f1 + f2 )) ”
  &&  emp
) \/
(
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ ((f1 + f2 ) <= 144) ” 
  &&  “ (f2 <= 89) ” 
  &&  “ (2 <= f2) ” 
  &&  “ (pf_after_advance_z count f2 (f1 + f2 ) ) ”
  &&  emp
).

Definition prime_fib_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ ((f1 + f2 ) <= 144) ”
.

Definition prime_fib_entail_wit_2_split_goal_2 := 
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (f2 <= 89) ”
.

Definition prime_fib_entail_wit_2_split_goal_3 := 
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (2 <= f2) ”
.

Definition prime_fib_entail_wit_2_split_goal_4 := 
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (pf_after_advance_z count f2 (f1 + f2 ) ) ”
.

Definition prime_fib_entail_wit_3 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (f2 <= 144)) (PreH12 : (m = f2)) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 10) ” 
  &&  “ (1 = 0) ” 
  &&  “ (prime_scan_state_z f1 2 1 ) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 10) ” 
  &&  “ (1 = 1) ” 
  &&  “ (prime_scan_state_z f1 2 1 ) ”
  &&  emp)
.

Definition prime_fib_entail_wit_4_1 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : ((f1 % ( w ) ) = 0)) (PreH2 : (w < 10)) (PreH3 : (w <= (f1 ÷ w ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (problem_39_pre_z n_pre )) (PreH8 : (prime_fib_safe_z n_pre )) (PreH9 : (0 <= count)) (PreH10 : (count < n_pre)) (PreH11 : (pf_after_advance_z count f1 f2 )) (PreH12 : (2 <= f1)) (PreH13 : (f1 <= 89)) (PreH14 : (m = f2)) (PreH15 : (2 <= w)) (PreH16 : (w <= 10)) (PreH17 : (isprime = 1)) (PreH18 : (prime_scan_state_z f1 w isprime )) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((0 <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((0 = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((0 <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((0 = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
.

Definition prime_fib_entail_wit_4_2 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : ((f1 % ( w ) ) = 0)) (PreH2 : (w < 10)) (PreH3 : (w <= (f1 ÷ w ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (problem_39_pre_z n_pre )) (PreH8 : (prime_fib_safe_z n_pre )) (PreH9 : (0 <= count)) (PreH10 : (count < n_pre)) (PreH11 : (pf_after_advance_z count f1 f2 )) (PreH12 : (2 <= f1)) (PreH13 : (f1 <= 89)) (PreH14 : (m = f2)) (PreH15 : (2 <= w)) (PreH16 : (w <= 10)) (PreH17 : (isprime = 0)) (PreH18 : (prime_scan_state_z f1 w isprime )) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((0 <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((0 = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((0 <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((0 = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
.

Definition prime_fib_entail_wit_4_3 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w >= 10)) (PreH2 : (w <= (f1 ÷ w ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_39_pre_z n_pre )) (PreH7 : (prime_fib_safe_z n_pre )) (PreH8 : (0 <= count)) (PreH9 : (count < n_pre)) (PreH10 : (pf_after_advance_z count f1 f2 )) (PreH11 : (2 <= f1)) (PreH12 : (f1 <= 89)) (PreH13 : (m = f2)) (PreH14 : (2 <= w)) (PreH15 : (w <= 10)) (PreH16 : (isprime = 1)) (PreH17 : (prime_scan_state_z f1 w isprime )) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
.

Definition prime_fib_entail_wit_4_4 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w >= 10)) (PreH2 : (w <= (f1 ÷ w ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 5)) (PreH5 : (n_pre < INT_MAX)) (PreH6 : (problem_39_pre_z n_pre )) (PreH7 : (prime_fib_safe_z n_pre )) (PreH8 : (0 <= count)) (PreH9 : (count < n_pre)) (PreH10 : (pf_after_advance_z count f1 f2 )) (PreH11 : (2 <= f1)) (PreH12 : (f1 <= 89)) (PreH13 : (m = f2)) (PreH14 : (2 <= w)) (PreH15 : (w <= 10)) (PreH16 : (isprime = 0)) (PreH17 : (prime_scan_state_z f1 w isprime )) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
.

Definition prime_fib_entail_wit_4_5 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w > (f1 ÷ w ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count < n_pre)) (PreH9 : (pf_after_advance_z count f1 f2 )) (PreH10 : (2 <= f1)) (PreH11 : (f1 <= 89)) (PreH12 : (m = f2)) (PreH13 : (2 <= w)) (PreH14 : (w <= 10)) (PreH15 : (isprime = 0)) (PreH16 : (prime_scan_state_z f1 w isprime )) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
.

Definition prime_fib_entail_wit_4_6 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (w > (f1 ÷ w ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count < n_pre)) (PreH9 : (pf_after_advance_z count f1 f2 )) (PreH10 : (2 <= f1)) (PreH11 : (f1 <= 89)) (PreH12 : (m = f2)) (PreH13 : (2 <= w)) (PreH14 : (w <= 10)) (PreH15 : (isprime = 1)) (PreH16 : (prime_scan_state_z f1 w isprime )) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ”
  &&  emp)
.

Definition prime_fib_entail_wit_5_1 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : ((f1 % ( w ) ) <> 0)) (PreH2 : (w < 10)) (PreH3 : (w <= (f1 ÷ w ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (problem_39_pre_z n_pre )) (PreH8 : (prime_fib_safe_z n_pre )) (PreH9 : (0 <= count)) (PreH10 : (count < n_pre)) (PreH11 : (pf_after_advance_z count f1 f2 )) (PreH12 : (2 <= f1)) (PreH13 : (f1 <= 89)) (PreH14 : (m = f2)) (PreH15 : (2 <= w)) (PreH16 : (w <= 10)) (PreH17 : (isprime = 0)) (PreH18 : (prime_scan_state_z f1 w isprime )) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= (w + 1 )) ” 
  &&  “ ((w + 1 ) <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ (prime_scan_state_z f1 (w + 1 ) isprime ) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= (w + 1 )) ” 
  &&  “ ((w + 1 ) <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ (prime_scan_state_z f1 (w + 1 ) isprime ) ”
  &&  emp)
.

Definition prime_fib_entail_wit_5_2 := 
forall (n_pre: Z) (isprime: Z) (w: Z) (m: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : ((f1 % ( w ) ) <> 0)) (PreH2 : (w < 10)) (PreH3 : (w <= (f1 ÷ w ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 5)) (PreH6 : (n_pre < INT_MAX)) (PreH7 : (problem_39_pre_z n_pre )) (PreH8 : (prime_fib_safe_z n_pre )) (PreH9 : (0 <= count)) (PreH10 : (count < n_pre)) (PreH11 : (pf_after_advance_z count f1 f2 )) (PreH12 : (2 <= f1)) (PreH13 : (f1 <= 89)) (PreH14 : (m = f2)) (PreH15 : (2 <= w)) (PreH16 : (w <= 10)) (PreH17 : (isprime = 1)) (PreH18 : (prime_scan_state_z f1 w isprime )) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= (w + 1 )) ” 
  &&  “ ((w + 1 ) <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ (prime_scan_state_z f1 (w + 1 ) isprime ) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= (w + 1 )) ” 
  &&  “ ((w + 1 ) <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ (prime_scan_state_z f1 (w + 1 ) isprime ) ”
  &&  emp)
.

Definition prime_fib_entail_wit_6_1 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 1)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime = 0)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ” 
  &&  “ (isprime = 0) ”
  &&  emp
.

Definition prime_fib_entail_wit_6_2 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 0)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime = 0)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ” 
  &&  “ (isprime = 0) ”
  &&  emp
.

Definition prime_fib_entail_wit_7_1 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 1)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime <> 0)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ” 
  &&  “ (isprime <> 0) ”
  &&  emp
.

Definition prime_fib_entail_wit_7_2 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 0)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime <> 0)) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < n_pre) ” 
  &&  “ (pf_after_advance_z count f1 f2 ) ” 
  &&  “ (2 <= f1) ” 
  &&  “ (f1 <= 89) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ ((isprime <> 0) -> (finite_prime_candidate_z f1 )) ” 
  &&  “ ((isprime = 0) -> ~((finite_prime_candidate_z f1 ))) ” 
  &&  “ (isprime <> 0) ”
  &&  emp
.

Definition prime_fib_entail_wit_8_1 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 0)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime = 0)) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= n_pre) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ (pf_loop_state_z count f1 f2 ) ” 
  &&  “ ((count = n_pre) -> (finite_prime_candidate_z f1 )) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= n_pre) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ (pf_loop_state_z count f1 f2 ) ” 
  &&  “ ((count = n_pre) -> (finite_prime_candidate_z f1 )) ”
  &&  emp)
.

Definition prime_fib_entail_wit_8_2 := 
forall (n_pre: Z) (count: Z) (f2: Z) (f1: Z) (m: Z) (w: Z) (isprime: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 5)) (PreH3 : (n_pre < INT_MAX)) (PreH4 : (problem_39_pre_z n_pre )) (PreH5 : (prime_fib_safe_z n_pre )) (PreH6 : (0 <= count)) (PreH7 : (count < n_pre)) (PreH8 : (pf_after_advance_z count f1 f2 )) (PreH9 : (2 <= f1)) (PreH10 : (f1 <= 89)) (PreH11 : (m = f2)) (PreH12 : (2 <= w)) (PreH13 : (w <= 10)) (PreH14 : (isprime = 1)) (PreH15 : ((isprime <> 0) -> (finite_prime_candidate_z f1 ))) (PreH16 : ((isprime = 0) -> ~((finite_prime_candidate_z f1 )))) (PreH17 : (isprime <> 0)) ,
  TT && emp 
|--
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= n_pre) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 1) ” 
  &&  “ (pf_loop_state_z (count + 1 ) f1 f2 ) ” 
  &&  “ (((count + 1 ) = n_pre) -> (finite_prime_candidate_z f1 )) ”
  &&  emp)
  ||
  (“ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= n_pre) ” 
  &&  “ (m = f2) ” 
  &&  “ (2 <= w) ” 
  &&  “ (w <= 10) ” 
  &&  “ (isprime = 0) ” 
  &&  “ (pf_loop_state_z (count + 1 ) f1 f2 ) ” 
  &&  “ (((count + 1 ) = n_pre) -> (finite_prime_candidate_z f1 )) ”
  &&  emp)
.

Definition prime_fib_entail_wit_9_1 := 
forall (n_pre: Z) (count: Z) (m: Z) (f2: Z) (w: Z) (isprime: Z) (f1: Z) (PreH1 : (count <> n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (m = f2)) (PreH10 : (2 <= w)) (PreH11 : (w <= 10)) (PreH12 : (isprime = 1)) (PreH13 : (pf_loop_state_z count f1 f2 )) (PreH14 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= n_pre) ” 
  &&  “ (pf_loop_state_z count f1 f2 ) ” 
  &&  “ ((count = n_pre) -> (finite_prime_candidate_z f1 )) ”
  &&  emp
.

Definition prime_fib_entail_wit_9_2 := 
forall (n_pre: Z) (count: Z) (m: Z) (f2: Z) (w: Z) (isprime: Z) (f1: Z) (PreH1 : (count <> n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (m = f2)) (PreH10 : (2 <= w)) (PreH11 : (w <= 10)) (PreH12 : (isprime = 0)) (PreH13 : (pf_loop_state_z count f1 f2 )) (PreH14 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 5) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (problem_39_pre_z n_pre ) ” 
  &&  “ (prime_fib_safe_z n_pre ) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= n_pre) ” 
  &&  “ (pf_loop_state_z count f1 f2 ) ” 
  &&  “ ((count = n_pre) -> (finite_prime_candidate_z f1 )) ”
  &&  emp
.

Definition prime_fib_return_wit_1 := 
(
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
  &&  emp
).

Definition prime_fib_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (f1: Z) (f2: Z) (count: Z) (PreH1 : (count >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (pf_loop_state_z count f1 f2 )) (PreH10 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
.

Definition prime_fib_return_wit_2 := 
(
forall (n_pre: Z) (count: Z) (m: Z) (f2: Z) (w: Z) (isprime: Z) (f1: Z) (PreH1 : (count = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (m = f2)) (PreH10 : (2 <= w)) (PreH11 : (w <= 10)) (PreH12 : (isprime = 1)) (PreH13 : (pf_loop_state_z count f1 f2 )) (PreH14 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (m: Z) (f2: Z) (w: Z) (isprime: Z) (f1: Z) (PreH1 : (count = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (m = f2)) (PreH10 : (2 <= w)) (PreH11 : (w <= 10)) (PreH12 : (isprime = 1)) (PreH13 : (pf_loop_state_z count f1 f2 )) (PreH14 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
  &&  emp
).

Definition prime_fib_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (count: Z) (m: Z) (f2: Z) (w: Z) (isprime: Z) (f1: Z) (PreH1 : (count = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (m = f2)) (PreH10 : (2 <= w)) (PreH11 : (w <= 10)) (PreH12 : (isprime = 1)) (PreH13 : (pf_loop_state_z count f1 f2 )) (PreH14 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
.

Definition prime_fib_return_wit_3 := 
(
forall (n_pre: Z) (count: Z) (m: Z) (f2: Z) (w: Z) (isprime: Z) (f1: Z) (PreH1 : (count = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (m = f2)) (PreH10 : (2 <= w)) (PreH11 : (w <= 10)) (PreH12 : (isprime = 0)) (PreH13 : (pf_loop_state_z count f1 f2 )) (PreH14 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (count: Z) (m: Z) (f2: Z) (w: Z) (isprime: Z) (f1: Z) (PreH1 : (count = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (m = f2)) (PreH10 : (2 <= w)) (PreH11 : (w <= 10)) (PreH12 : (isprime = 0)) (PreH13 : (pf_loop_state_z count f1 f2 )) (PreH14 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
  &&  emp
).

Definition prime_fib_return_wit_3_split_goal_1 := 
forall (n_pre: Z) (count: Z) (m: Z) (f2: Z) (w: Z) (isprime: Z) (f1: Z) (PreH1 : (count = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 5)) (PreH4 : (n_pre < INT_MAX)) (PreH5 : (problem_39_pre_z n_pre )) (PreH6 : (prime_fib_safe_z n_pre )) (PreH7 : (0 <= count)) (PreH8 : (count <= n_pre)) (PreH9 : (m = f2)) (PreH10 : (2 <= w)) (PreH11 : (w <= 10)) (PreH12 : (isprime = 0)) (PreH13 : (pf_loop_state_z count f1 f2 )) (PreH14 : ((count = n_pre) -> (finite_prime_candidate_z f1 ))) ,
  TT && emp 
|--
  “ (problem_39_spec_z n_pre f1 ) ”
.

Module Type VC_Correct.


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
Axiom proof_of_prime_fib_safety_wit_16 : prime_fib_safety_wit_16.
Axiom proof_of_prime_fib_safety_wit_17 : prime_fib_safety_wit_17.
Axiom proof_of_prime_fib_safety_wit_18 : prime_fib_safety_wit_18.
Axiom proof_of_prime_fib_safety_wit_19 : prime_fib_safety_wit_19.
Axiom proof_of_prime_fib_safety_wit_20 : prime_fib_safety_wit_20.
Axiom proof_of_prime_fib_safety_wit_21 : prime_fib_safety_wit_21.
Axiom proof_of_prime_fib_safety_wit_22 : prime_fib_safety_wit_22.
Axiom proof_of_prime_fib_entail_wit_1 : prime_fib_entail_wit_1.
Axiom proof_of_prime_fib_entail_wit_2 : prime_fib_entail_wit_2.
Axiom proof_of_prime_fib_entail_wit_3 : prime_fib_entail_wit_3.
Axiom proof_of_prime_fib_entail_wit_4_1 : prime_fib_entail_wit_4_1.
Axiom proof_of_prime_fib_entail_wit_4_2 : prime_fib_entail_wit_4_2.
Axiom proof_of_prime_fib_entail_wit_4_3 : prime_fib_entail_wit_4_3.
Axiom proof_of_prime_fib_entail_wit_4_4 : prime_fib_entail_wit_4_4.
Axiom proof_of_prime_fib_entail_wit_4_5 : prime_fib_entail_wit_4_5.
Axiom proof_of_prime_fib_entail_wit_4_6 : prime_fib_entail_wit_4_6.
Axiom proof_of_prime_fib_entail_wit_5_1 : prime_fib_entail_wit_5_1.
Axiom proof_of_prime_fib_entail_wit_5_2 : prime_fib_entail_wit_5_2.
Axiom proof_of_prime_fib_entail_wit_6_1 : prime_fib_entail_wit_6_1.
Axiom proof_of_prime_fib_entail_wit_6_2 : prime_fib_entail_wit_6_2.
Axiom proof_of_prime_fib_entail_wit_7_1 : prime_fib_entail_wit_7_1.
Axiom proof_of_prime_fib_entail_wit_7_2 : prime_fib_entail_wit_7_2.
Axiom proof_of_prime_fib_entail_wit_8_1 : prime_fib_entail_wit_8_1.
Axiom proof_of_prime_fib_entail_wit_8_2 : prime_fib_entail_wit_8_2.
Axiom proof_of_prime_fib_entail_wit_9_1 : prime_fib_entail_wit_9_1.
Axiom proof_of_prime_fib_entail_wit_9_2 : prime_fib_entail_wit_9_2.
Axiom proof_of_prime_fib_return_wit_1 : prime_fib_return_wit_1.
Axiom proof_of_prime_fib_return_wit_2 : prime_fib_return_wit_2.
Axiom proof_of_prime_fib_return_wit_3 : prime_fib_return_wit_3.

End VC_Correct.
