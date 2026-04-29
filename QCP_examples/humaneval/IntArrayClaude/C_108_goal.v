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
Require Import coins_108.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function abs -----*)

Definition abs_safety_wit_1 := 
forall (x_pre: Z) ,
  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition abs_safety_wit_2 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  [| (x_pre <> (INT_MIN)) |]
.

Definition abs_return_wit_1 := 
forall (x_pre: Z) ,
  [| (x_pre >= 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| (x_pre = (Zabs (x_pre))) |]
  &&  emp
.

Definition abs_return_wit_2 := 
forall (x_pre: Z) ,
  [| (x_pre < 0) |] 
  &&  [| (INT_MIN < x_pre) |] 
  &&  [| (x_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((-x_pre) = (Zabs (x_pre))) |]
  &&  emp
.

(*----- Function count_nums -----*)

Definition count_nums_safety_wit_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_nums_safety_wit_2 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_nums_safety_wit_3 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_nums_safety_wit_4 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| ((num + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num + 1 )) |]
.

Definition count_nums_safety_wit_5 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_nums_safety_wit_6 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_nums_safety_wit_7 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition count_nums_safety_wit_8 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (w >= 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((sum + (w % ( 10 ) ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum + (w % ( 10 ) ) )) |]
.

Definition count_nums_safety_wit_9 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (w >= 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((w <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition count_nums_safety_wit_10 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (w >= 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition count_nums_safety_wit_11 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (w >= 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (w % ( 10 ) ) ))
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((w <> (INT_MIN)) \/ (10 <> (-1))) |] 
  &&  [| (10 <> 0) |]
.

Definition count_nums_safety_wit_12 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (w >= 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (w % ( 10 ) ) ))
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition count_nums_safety_wit_13 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (w < 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((sum - w ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (sum - w )) |]
.

Definition count_nums_safety_wit_14 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (w < 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> (sum - w ))
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_nums_safety_wit_15 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| ((sum - w ) > 0) |] 
  &&  [| (w < 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> (sum - w ))
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((num + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num + 1 )) |]
.

Definition count_nums_safety_wit_16 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| ((sum - w ) > 0) |] 
  &&  [| (w < 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> (sum - w ))
  **  ((( &( "w" ) )) # Int  |-> w)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_nums_safety_wit_17 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| ((sum - w ) <= 0) |] 
  &&  [| (w < 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_nums_safety_wit_18 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| ((sum - w ) > 0) |] 
  &&  [| (w < 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> (num + 1 ))
  **  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_nums_safety_wit_19 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> (num + 1 ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_nums_entail_wit_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (count_nums_prefix 0 input_l 0 ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_entail_wit_2 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) (retval: Z) ,
  [| (retval = (Zabs ((Znth i input_l 0)))) |] 
  &&  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) retval 0 ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_entail_wit_3 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| (w >= 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) (w ÷ 10 ) (sum + (w % ( 10 ) ) ) ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_entail_wit_4_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) > 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_size_pre) |] 
  &&  [| (count_nums_prefix (i + 1 ) input_l (num + 1 ) ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_entail_wit_4_2 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| ((sum - w ) > 0) |] 
  &&  [| (w < 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_size_pre) |] 
  &&  [| (count_nums_prefix (i + 1 ) input_l (num + 1 ) ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_entail_wit_4_3 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (w: Z) (sum: Z) (num: Z) (i: Z) ,
  [| ((sum - w ) <= 0) |] 
  &&  [| (w < 10) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |] 
  &&  [| ((Znth (i) (input_l) (0)) <= 0) |] 
  &&  [| (digit_scan_state (Zabs ((Znth (i) (input_l) (0)))) w sum ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_size_pre) |] 
  &&  [| (count_nums_prefix (i + 1 ) input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_return_wit_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| (i >= n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (problem_108_spec_z input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_partial_solve_wit_1 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (((n_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i n_pre i 0 n_size_pre input_l )
.

Definition count_nums_partial_solve_wit_2 := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (((n_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i n_pre i 0 n_size_pre input_l )
.

Definition count_nums_partial_solve_wit_3_pure := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
  **  ((( &( "w" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Ptr  |-> n_pre)
  **  ((( &( "n_size" ) )) # Int  |-> n_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  [| ((Znth i input_l 0) <= INT_MAX) |] 
  &&  [| (INT_MIN < (Znth i input_l 0)) |]
.

Definition count_nums_partial_solve_wit_3_aux := 
forall (n_size_pre: Z) (n_pre: Z) (input_l: (@list Z)) (num: Z) (i: Z) ,
  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
|--
  [| ((Znth i input_l 0) <= INT_MAX) |] 
  &&  [| (INT_MIN < (Znth i input_l 0)) |] 
  &&  [| ((Znth i input_l 0) <= 0) |] 
  &&  [| (i < n_size_pre) |] 
  &&  [| (0 <= n_size_pre) |] 
  &&  [| (n_size_pre < INT_MAX) |] 
  &&  [| (n_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_108_pre_z input_l ) |] 
  &&  [| (count_nums_int_range input_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_size_pre) |] 
  &&  [| (count_nums_prefix i input_l num ) |]
  &&  (IntArray.full n_pre n_size_pre input_l )
.

Definition count_nums_partial_solve_wit_3 := count_nums_partial_solve_wit_3_pure -> count_nums_partial_solve_wit_3_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_count_nums_safety_wit_1 : count_nums_safety_wit_1.
Axiom proof_of_count_nums_safety_wit_2 : count_nums_safety_wit_2.
Axiom proof_of_count_nums_safety_wit_3 : count_nums_safety_wit_3.
Axiom proof_of_count_nums_safety_wit_4 : count_nums_safety_wit_4.
Axiom proof_of_count_nums_safety_wit_5 : count_nums_safety_wit_5.
Axiom proof_of_count_nums_safety_wit_6 : count_nums_safety_wit_6.
Axiom proof_of_count_nums_safety_wit_7 : count_nums_safety_wit_7.
Axiom proof_of_count_nums_safety_wit_8 : count_nums_safety_wit_8.
Axiom proof_of_count_nums_safety_wit_9 : count_nums_safety_wit_9.
Axiom proof_of_count_nums_safety_wit_10 : count_nums_safety_wit_10.
Axiom proof_of_count_nums_safety_wit_11 : count_nums_safety_wit_11.
Axiom proof_of_count_nums_safety_wit_12 : count_nums_safety_wit_12.
Axiom proof_of_count_nums_safety_wit_13 : count_nums_safety_wit_13.
Axiom proof_of_count_nums_safety_wit_14 : count_nums_safety_wit_14.
Axiom proof_of_count_nums_safety_wit_15 : count_nums_safety_wit_15.
Axiom proof_of_count_nums_safety_wit_16 : count_nums_safety_wit_16.
Axiom proof_of_count_nums_safety_wit_17 : count_nums_safety_wit_17.
Axiom proof_of_count_nums_safety_wit_18 : count_nums_safety_wit_18.
Axiom proof_of_count_nums_safety_wit_19 : count_nums_safety_wit_19.
Axiom proof_of_count_nums_entail_wit_1 : count_nums_entail_wit_1.
Axiom proof_of_count_nums_entail_wit_2 : count_nums_entail_wit_2.
Axiom proof_of_count_nums_entail_wit_3 : count_nums_entail_wit_3.
Axiom proof_of_count_nums_entail_wit_4_1 : count_nums_entail_wit_4_1.
Axiom proof_of_count_nums_entail_wit_4_2 : count_nums_entail_wit_4_2.
Axiom proof_of_count_nums_entail_wit_4_3 : count_nums_entail_wit_4_3.
Axiom proof_of_count_nums_return_wit_1 : count_nums_return_wit_1.
Axiom proof_of_count_nums_partial_solve_wit_1 : count_nums_partial_solve_wit_1.
Axiom proof_of_count_nums_partial_solve_wit_2 : count_nums_partial_solve_wit_2.
Axiom proof_of_count_nums_partial_solve_wit_3_pure : count_nums_partial_solve_wit_3_pure.
Axiom proof_of_count_nums_partial_solve_wit_3 : count_nums_partial_solve_wit_3.

End VC_Correct.
