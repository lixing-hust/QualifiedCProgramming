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
Require Import coins_122.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function add_elements -----*)

Definition add_elements_safety_wit_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |]
  &&  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition add_elements_safety_wit_2 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition add_elements_safety_wit_3 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (99 <> (INT_MIN)) |]
.

Definition add_elements_safety_wit_4 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (99 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 99) |]
.

Definition add_elements_safety_wit_5 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (99 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 99) |]
.

Definition add_elements_safety_wit_6 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) <= 99) |] 
  &&  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| ((s + (Znth i lv 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s + (Znth i lv 0) )) |]
.

Definition add_elements_safety_wit_7 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) > 99) |] 
  &&  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition add_elements_safety_wit_8 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) < (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition add_elements_safety_wit_9 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) <= 99) |] 
  &&  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (Znth i lv 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition add_elements_entail_wit_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= k_pre) |] 
  &&  [| (0 = (sum_two_digit_upto (0) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition add_elements_entail_wit_2_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) <= 99) |] 
  &&  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= k_pre) |] 
  &&  [| ((s + (Znth i lv 0) ) = (sum_two_digit_upto ((i + 1 )) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition add_elements_entail_wit_2_2 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) < (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto ((i + 1 )) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition add_elements_entail_wit_2_3 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) > 99) |] 
  &&  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto ((i + 1 )) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition add_elements_return_wit_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i >= k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (problem_122_spec_z lv k_pre s ) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition add_elements_partial_solve_wit_1 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre lv )
.

Definition add_elements_partial_solve_wit_2 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre lv )
.

Definition add_elements_partial_solve_wit_3 := 
forall (k_pre: Z) (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) <= 99) |] 
  &&  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| ((Znth i lv 0) <= 99) |] 
  &&  [| ((Znth i lv 0) >= (-99)) |] 
  &&  [| (i < k_pre) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (1 <= k_pre) |] 
  &&  [| (k_pre <= arr_size_pre) |] 
  &&  [| (arr_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_122_pre_z lv k_pre ) |] 
  &&  [| (sum_two_digit_int_range k_pre lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= k_pre) |] 
  &&  [| (s = (sum_two_digit_upto (i) (lv))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre lv )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_add_elements_safety_wit_1 : add_elements_safety_wit_1.
Axiom proof_of_add_elements_safety_wit_2 : add_elements_safety_wit_2.
Axiom proof_of_add_elements_safety_wit_3 : add_elements_safety_wit_3.
Axiom proof_of_add_elements_safety_wit_4 : add_elements_safety_wit_4.
Axiom proof_of_add_elements_safety_wit_5 : add_elements_safety_wit_5.
Axiom proof_of_add_elements_safety_wit_6 : add_elements_safety_wit_6.
Axiom proof_of_add_elements_safety_wit_7 : add_elements_safety_wit_7.
Axiom proof_of_add_elements_safety_wit_8 : add_elements_safety_wit_8.
Axiom proof_of_add_elements_safety_wit_9 : add_elements_safety_wit_9.
Axiom proof_of_add_elements_entail_wit_1 : add_elements_entail_wit_1.
Axiom proof_of_add_elements_entail_wit_2_1 : add_elements_entail_wit_2_1.
Axiom proof_of_add_elements_entail_wit_2_2 : add_elements_entail_wit_2_2.
Axiom proof_of_add_elements_entail_wit_2_3 : add_elements_entail_wit_2_3.
Axiom proof_of_add_elements_return_wit_1 : add_elements_return_wit_1.
Axiom proof_of_add_elements_partial_solve_wit_1 : add_elements_partial_solve_wit_1.
Axiom proof_of_add_elements_partial_solve_wit_2 : add_elements_partial_solve_wit_2.
Axiom proof_of_add_elements_partial_solve_wit_3 : add_elements_partial_solve_wit_3.

End VC_Correct.
