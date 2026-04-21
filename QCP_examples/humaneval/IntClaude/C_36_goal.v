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
Require Import coins_36.
Local Open Scope sac.

(*----- Function fizz_buzz -----*)

Definition fizz_buzz_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fizz_buzz_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fizz_buzz_safety_wit_3 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i <> (INT_MIN)) \/ (11 <> (-1))) |] 
  &&  [| (11 <> 0) |]
.

Definition fizz_buzz_safety_wit_4 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (11 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 11) |]
.

Definition fizz_buzz_safety_wit_5 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fizz_buzz_safety_wit_6 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fizz_buzz_safety_wit_7 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((q <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition fizz_buzz_safety_wit_8 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition fizz_buzz_safety_wit_9 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition fizz_buzz_safety_wit_10 := 
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count_2 = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| (count_2 <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition fizz_buzz_safety_wit_11 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fizz_buzz_safety_wit_12 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) <> 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((q <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition fizz_buzz_safety_wit_13 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) <> 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition fizz_buzz_safety_wit_14 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> (count_2 + 1 ))
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((q <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition fizz_buzz_safety_wit_15 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> (count_2 + 1 ))
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition fizz_buzz_safety_wit_16 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i <> (INT_MIN)) \/ (13 <> (-1))) |] 
  &&  [| (13 <> 0) |]
.

Definition fizz_buzz_safety_wit_17 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (13 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 13) |]
.

Definition fizz_buzz_safety_wit_18 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fizz_buzz_safety_wit_19 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition fizz_buzz_safety_wit_20 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((q <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition fizz_buzz_safety_wit_21 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition fizz_buzz_safety_wit_22 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (7 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 7) |]
.

Definition fizz_buzz_safety_wit_23 := 
forall (n_pre: Z) (count_2: Z) (i: Z) (q: Z) (count: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count_2 = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| (count_2 <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((count + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (count + 1 )) |]
.

Definition fizz_buzz_safety_wit_24 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition fizz_buzz_safety_wit_25 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) <> 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((q <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition fizz_buzz_safety_wit_26 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) <> 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition fizz_buzz_safety_wit_27 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> (count_2 + 1 ))
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((q <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition fizz_buzz_safety_wit_28 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "count" ) )) # Int  |-> (count_2 + 1 ))
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition fizz_buzz_safety_wit_29 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| ((i % ( 13 ) ) <> 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fizz_buzz_safety_wit_30 := 
forall (n_pre: Z) (count: Z) (i_2: Z) (q: Z) (count_2: Z) (i: Z) ,
  [| (q <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i * (i + 1 ) )) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i_2))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i_2 * i_2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fizz_buzz_safety_wit_31 := 
forall (n_pre: Z) (count: Z) (i_2: Z) (q: Z) (count_2: Z) (i: Z) ,
  [| (q <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i * (i + 1 ) )) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i_2))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i_2 * i_2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count_2)
  **  ((( &( "q" ) )) # Int  |-> q)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition fizz_buzz_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = (fizzbuzz_upto (0))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (0 * 0 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
.

Definition fizz_buzz_entail_wit_2 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((count + (count_digit7 (i)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) )) |] 
  &&  [| ((count + (count_digit7 (i)) ) <= (i * (i + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
.

Definition fizz_buzz_entail_wit_3_1 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= (count_2 + 1 )) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= (q ÷ 10 )) |] 
  &&  [| (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
.

Definition fizz_buzz_entail_wit_3_2 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) <> 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (0 <= (q ÷ 10 )) |] 
  &&  [| ((count_2 + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
.

Definition fizz_buzz_entail_wit_4 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= i) |] 
  &&  [| ((count + (count_digit7 (i)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) )) |] 
  &&  [| ((count + (count_digit7 (i)) ) <= (i * (i + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
.

Definition fizz_buzz_entail_wit_5_1 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) = 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= (count_2 + 1 )) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= (q ÷ 10 )) |] 
  &&  [| (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| (((count_2 + 1 ) + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
.

Definition fizz_buzz_entail_wit_5_2 := 
forall (n_pre: Z) (count: Z) (i: Z) (q: Z) (count_2: Z) (i_2: Z) ,
  [| ((q % ( 10 ) ) <> 7) |] 
  &&  [| (q > 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 (q)) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= (q ÷ 10 )) |] 
  &&  [| ((count_2 + (count_digit7 ((q ÷ 10 ))) ) = ((fizzbuzz_upto (i_2)) + (count_digit7 (i_2)) )) |] 
  &&  [| ((count_2 + (count_digit7 ((q ÷ 10 ))) ) <= (i_2 * (i_2 + 1 ) )) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
.

Definition fizz_buzz_entail_wit_6_1 := 
forall (n_pre: Z) (count_2: Z) (i_2: Z) (q: Z) (count: Z) (i: Z) ,
  [| (q <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| ((i % ( 11 ) ) = 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) )) |] 
  &&  [| ((count + (count_digit7 (q)) ) <= (i * (i + 1 ) )) |] 
  &&  [| ((i_2 % ( 11 ) ) = 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (count_2 = (fizzbuzz_upto (i_2))) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| (count_2 <= (i_2 * i_2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "q" ) )) # Int  |-> q)
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto ((i + 1 )))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= ((i + 1 ) * (i + 1 ) )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "q" ) )) # Int  |->_)
.

Definition fizz_buzz_entail_wit_6_2 := 
forall (n_pre: Z) (count_2: Z) (i_2: Z) (q: Z) (count: Z) (i: Z) ,
  [| (q <= 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= count) |] 
  &&  [| ((i % ( 13 ) ) = 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (0 <= q) |] 
  &&  [| ((count + (count_digit7 (q)) ) = ((fizzbuzz_upto (i)) + (count_digit7 (i)) )) |] 
  &&  [| ((count + (count_digit7 (q)) ) <= (i * (i + 1 ) )) |] 
  &&  [| ((i_2 % ( 13 ) ) = 0) |] 
  &&  [| ((i_2 % ( 11 ) ) <> 0) |] 
  &&  [| (i_2 < n_pre) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 <= n_pre) |] 
  &&  [| (count_2 = (fizzbuzz_upto (i_2))) |] 
  &&  [| (0 <= count_2) |] 
  &&  [| (count_2 <= (i_2 * i_2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "q" ) )) # Int  |-> q)
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto ((i + 1 )))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= ((i + 1 ) * (i + 1 ) )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "q" ) )) # Int  |->_)
.

Definition fizz_buzz_entail_wit_6_3 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| ((i % ( 13 ) ) <> 0) |] 
  &&  [| ((i % ( 11 ) ) <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto ((i + 1 )))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= ((i + 1 ) * (i + 1 ) )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
.

Definition fizz_buzz_return_wit_1 := 
forall (n_pre: Z) (count: Z) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (count = (fizzbuzz_upto (i))) |] 
  &&  [| (0 <= count) |] 
  &&  [| (count <= (i * i )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (problem_36_spec_z n_pre count ) |]
  &&  emp
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
Axiom proof_of_fizz_buzz_safety_wit_24 : fizz_buzz_safety_wit_24.
Axiom proof_of_fizz_buzz_safety_wit_25 : fizz_buzz_safety_wit_25.
Axiom proof_of_fizz_buzz_safety_wit_26 : fizz_buzz_safety_wit_26.
Axiom proof_of_fizz_buzz_safety_wit_27 : fizz_buzz_safety_wit_27.
Axiom proof_of_fizz_buzz_safety_wit_28 : fizz_buzz_safety_wit_28.
Axiom proof_of_fizz_buzz_safety_wit_29 : fizz_buzz_safety_wit_29.
Axiom proof_of_fizz_buzz_safety_wit_30 : fizz_buzz_safety_wit_30.
Axiom proof_of_fizz_buzz_safety_wit_31 : fizz_buzz_safety_wit_31.
Axiom proof_of_fizz_buzz_entail_wit_1 : fizz_buzz_entail_wit_1.
Axiom proof_of_fizz_buzz_entail_wit_2 : fizz_buzz_entail_wit_2.
Axiom proof_of_fizz_buzz_entail_wit_3_1 : fizz_buzz_entail_wit_3_1.
Axiom proof_of_fizz_buzz_entail_wit_3_2 : fizz_buzz_entail_wit_3_2.
Axiom proof_of_fizz_buzz_entail_wit_4 : fizz_buzz_entail_wit_4.
Axiom proof_of_fizz_buzz_entail_wit_5_1 : fizz_buzz_entail_wit_5_1.
Axiom proof_of_fizz_buzz_entail_wit_5_2 : fizz_buzz_entail_wit_5_2.
Axiom proof_of_fizz_buzz_entail_wit_6_1 : fizz_buzz_entail_wit_6_1.
Axiom proof_of_fizz_buzz_entail_wit_6_2 : fizz_buzz_entail_wit_6_2.
Axiom proof_of_fizz_buzz_entail_wit_6_3 : fizz_buzz_entail_wit_6_3.
Axiom proof_of_fizz_buzz_return_wit_1 : fizz_buzz_return_wit_1.

End VC_Correct.
