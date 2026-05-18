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
Require Import coins_123.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function get_odd_collatz -----*)

Definition get_odd_collatz_safety_wit_1 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition get_odd_collatz_safety_wit_2 := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1024 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1024) |]
.

Definition get_odd_collatz_safety_wit_3 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 1024 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition get_odd_collatz_safety_wit_4 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 1024 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition get_odd_collatz_safety_wit_5 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 1024 )
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((0 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 1 )) |]
.

Definition get_odd_collatz_safety_wit_6 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 1024 )
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition get_odd_collatz_safety_wit_7 := 
forall (n_pre: Z) (output_l: (@list Z)) (output_size: Z) (n: Z) (data: Z) (out: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition get_odd_collatz_safety_wit_8 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| ((n <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition get_odd_collatz_safety_wit_9 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition get_odd_collatz_safety_wit_10 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition get_odd_collatz_safety_wit_11 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> n)
  **  (IntArray.undef_seg data (output_size + 1 ) 1024 )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition get_odd_collatz_safety_wit_12 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre ((n * 3 ) + 1 ) output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (((n * 3 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((n * 3 ) + 1 )) |]
.

Definition get_odd_collatz_safety_wit_13 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre ((n * 3 ) + 1 ) output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n * 3 )) |]
.

Definition get_odd_collatz_safety_wit_14 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre ((n * 3 ) + 1 ) output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (3 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 3) |]
.

Definition get_odd_collatz_safety_wit_15 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre ((n * 3 ) + 1 ) output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition get_odd_collatz_safety_wit_16 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| ((n % ( 2 ) ) <> 1) |] 
  &&  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| ((n <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition get_odd_collatz_safety_wit_17 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| ((n % ( 2 ) ) <> 1) |] 
  &&  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition get_odd_collatz_safety_wit_18 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "n" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (1024 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1024) |]
.

Definition get_odd_collatz_safety_wit_19 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "n" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition get_odd_collatz_entail_wit_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 1024 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 < (0 + 1 )) |] 
  &&  [| ((0 + 1 ) <= 1024) |] 
  &&  [| ((0 + 1 ) = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n_pre output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg retval_2 0 (0 + 1 ) output_l )
  **  (IntArray.undef_seg retval_2 (0 + 1 ) 1024 )
.

Definition get_odd_collatz_entail_wit_2 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (output_size: Z) (n: Z) (data: Z) (out: Z) ,
  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  EX (output_l: (@list Z)) ,
  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
.

Definition get_odd_collatz_entail_wit_3 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  EX (output_l: (@list Z)) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
.

Definition get_odd_collatz_entail_wit_4 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l_2 ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> n)
  **  (IntArray.undef_seg data (output_size + 1 ) 1024 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
|--
  EX (output_l: (@list Z)) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) <= 1024) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre ((n * 3 ) + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) 1024 )
.

Definition get_odd_collatz_entail_wit_5_1 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| ((n % ( 2 ) ) <> 1) |] 
  &&  [| (n <> 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < (n ÷ 2 )) |] 
  &&  [| ((n ÷ 2 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre (n ÷ 2 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
.

Definition get_odd_collatz_entail_wit_5_2 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < (n * 3 )) |] 
  &&  [| ((n * 3 ) <= INT_MAX) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (odd_collatz_prefix n_pre ((n * 3 ) + 1 ) output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < ((n * 3 ) + 1 )) |] 
  &&  [| (((n * 3 ) + 1 ) < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre ((n * 3 ) + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
.

Definition get_odd_collatz_entail_wit_6 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (output_size: Z) (n: Z) (data: Z) (out: Z) ,
  [| (n = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < n) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l_2 ) |]
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
.

Definition get_odd_collatz_entail_wit_7 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (output_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) ,
  [| (output_size = (Zlength (sorted_l_2))) |] 
  &&  [| (1024 = (Zlength (sorted_full_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (0 <= 1024) |] 
  &&  [| (1024 < INT_MAX) |] 
  &&  [| ((sublist (0) (output_size) (sorted_full_l)) = sorted_l_2) |] 
  &&  [| (sorted_int_list_by 1 sorted_l_2 ) |] 
  &&  [| (Permutation output_l_2 sorted_l_2 ) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l_2 ) |]
  &&  (IntArray.full data 1024 sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (data_l: (@list Z))  (sorted_l: (@list Z))  (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size = (Zlength (sorted_l))) |] 
  &&  [| (1024 = (Zlength (data_l))) |] 
  &&  [| ((sublist (0) (output_size) (data_l)) = sorted_l) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation output_l sorted_l ) |] 
  &&  [| (problem_123_spec_z n_pre sorted_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full data 1024 data_l )
.

Definition get_odd_collatz_return_wit_1 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (sorted_l: (@list Z)) (data_l_2: (@list Z)) (out: Z) (data_2: Z) (output_size_2: Z) ,
  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size_2) |] 
  &&  [| (output_size_2 <= 1024) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_size_2 = (Zlength (sorted_l))) |] 
  &&  [| (1024 = (Zlength (data_l_2))) |] 
  &&  [| ((sublist (0) (output_size_2) (data_l_2)) = sorted_l) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l_2 ) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation output_l_2 sorted_l ) |] 
  &&  [| (problem_123_spec_z n_pre sorted_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.full data_2 1024 data_l_2 )
|--
  EX (data_l: (@list Z))  (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (1024 = (Zlength (data_l))) |] 
  &&  [| ((sublist (0) (output_size) (data_l)) = output_l) |] 
  &&  [| (problem_123_spec_z n_pre output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data 1024 data_l )
.

Definition get_odd_collatz_partial_solve_wit_1 := 
forall (n_pre: Z) ,
  [| (problem_123_pre_z n_pre ) |]
  &&  emp
|--
  [| (problem_123_pre_z n_pre ) |]
  &&  emp
.

Definition get_odd_collatz_partial_solve_wit_2_pure := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1024 >= 0) |] 
  &&  [| (1024 < INT_MAX) |]
.

Definition get_odd_collatz_partial_solve_wit_2_aux := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (1024 >= 0) |] 
  &&  [| (1024 < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition get_odd_collatz_partial_solve_wit_2 := get_odd_collatz_partial_solve_wit_2_pure -> get_odd_collatz_partial_solve_wit_2_aux.

Definition get_odd_collatz_partial_solve_wit_3 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  (IntArray.undef_full retval_2 1024 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 1024 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition get_odd_collatz_partial_solve_wit_4 := 
forall (n_pre: Z) (output_l: (@list Z)) (n: Z) (out: Z) (data: Z) (output_size: Z) ,
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (n <> 1) |] 
  &&  [| ((n % ( 2 ) ) = 1) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (INT_MIN <= n) |] 
  &&  [| (0 < n) |] 
  &&  [| (n <= INT_MAX) |] 
  &&  [| (n < INT_MAX) |] 
  &&  [| (output_size < 1024) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre n output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) 1024 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition get_odd_collatz_partial_solve_wit_5_pure := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "n" ) )) # Int  |-> 1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (data <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (0 <= 1024) |] 
  &&  [| (1024 < INT_MAX) |]
.

Definition get_odd_collatz_partial_solve_wit_5_aux := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
|--
  [| (data <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (0 <= 1024) |] 
  &&  [| (1024 < INT_MAX) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_123_pre_z n_pre ) |] 
  &&  [| (0 < output_size) |] 
  &&  [| (output_size <= 1024) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (odd_collatz_prefix n_pre 1 output_l ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 1024 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition get_odd_collatz_partial_solve_wit_5 := get_odd_collatz_partial_solve_wit_5_pure -> get_odd_collatz_partial_solve_wit_5_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_get_odd_collatz_safety_wit_1 : get_odd_collatz_safety_wit_1.
Axiom proof_of_get_odd_collatz_safety_wit_2 : get_odd_collatz_safety_wit_2.
Axiom proof_of_get_odd_collatz_safety_wit_3 : get_odd_collatz_safety_wit_3.
Axiom proof_of_get_odd_collatz_safety_wit_4 : get_odd_collatz_safety_wit_4.
Axiom proof_of_get_odd_collatz_safety_wit_5 : get_odd_collatz_safety_wit_5.
Axiom proof_of_get_odd_collatz_safety_wit_6 : get_odd_collatz_safety_wit_6.
Axiom proof_of_get_odd_collatz_safety_wit_7 : get_odd_collatz_safety_wit_7.
Axiom proof_of_get_odd_collatz_safety_wit_8 : get_odd_collatz_safety_wit_8.
Axiom proof_of_get_odd_collatz_safety_wit_9 : get_odd_collatz_safety_wit_9.
Axiom proof_of_get_odd_collatz_safety_wit_10 : get_odd_collatz_safety_wit_10.
Axiom proof_of_get_odd_collatz_safety_wit_11 : get_odd_collatz_safety_wit_11.
Axiom proof_of_get_odd_collatz_safety_wit_12 : get_odd_collatz_safety_wit_12.
Axiom proof_of_get_odd_collatz_safety_wit_13 : get_odd_collatz_safety_wit_13.
Axiom proof_of_get_odd_collatz_safety_wit_14 : get_odd_collatz_safety_wit_14.
Axiom proof_of_get_odd_collatz_safety_wit_15 : get_odd_collatz_safety_wit_15.
Axiom proof_of_get_odd_collatz_safety_wit_16 : get_odd_collatz_safety_wit_16.
Axiom proof_of_get_odd_collatz_safety_wit_17 : get_odd_collatz_safety_wit_17.
Axiom proof_of_get_odd_collatz_safety_wit_18 : get_odd_collatz_safety_wit_18.
Axiom proof_of_get_odd_collatz_safety_wit_19 : get_odd_collatz_safety_wit_19.
Axiom proof_of_get_odd_collatz_entail_wit_1 : get_odd_collatz_entail_wit_1.
Axiom proof_of_get_odd_collatz_entail_wit_2 : get_odd_collatz_entail_wit_2.
Axiom proof_of_get_odd_collatz_entail_wit_3 : get_odd_collatz_entail_wit_3.
Axiom proof_of_get_odd_collatz_entail_wit_4 : get_odd_collatz_entail_wit_4.
Axiom proof_of_get_odd_collatz_entail_wit_5_1 : get_odd_collatz_entail_wit_5_1.
Axiom proof_of_get_odd_collatz_entail_wit_5_2 : get_odd_collatz_entail_wit_5_2.
Axiom proof_of_get_odd_collatz_entail_wit_6 : get_odd_collatz_entail_wit_6.
Axiom proof_of_get_odd_collatz_entail_wit_7 : get_odd_collatz_entail_wit_7.
Axiom proof_of_get_odd_collatz_return_wit_1 : get_odd_collatz_return_wit_1.
Axiom proof_of_get_odd_collatz_partial_solve_wit_1 : get_odd_collatz_partial_solve_wit_1.
Axiom proof_of_get_odd_collatz_partial_solve_wit_2_pure : get_odd_collatz_partial_solve_wit_2_pure.
Axiom proof_of_get_odd_collatz_partial_solve_wit_2 : get_odd_collatz_partial_solve_wit_2.
Axiom proof_of_get_odd_collatz_partial_solve_wit_3 : get_odd_collatz_partial_solve_wit_3.
Axiom proof_of_get_odd_collatz_partial_solve_wit_4 : get_odd_collatz_partial_solve_wit_4.
Axiom proof_of_get_odd_collatz_partial_solve_wit_5_pure : get_odd_collatz_partial_solve_wit_5_pure.
Axiom proof_of_get_odd_collatz_partial_solve_wit_5 : get_odd_collatz_partial_solve_wit_5.

End VC_Correct.
