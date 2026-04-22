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
Require Import coins_68.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function pluck -----*)

Definition pluck_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition pluck_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| False |]
.

Definition pluck_safety_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| False |]
.

Definition pluck_safety_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| False |]
.

Definition pluck_safety_wit_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| False |]
.

Definition pluck_safety_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| (((Znth i input_l 0) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition pluck_safety_wit_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| (((Znth i input_l 0) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition pluck_safety_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition pluck_safety_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition pluck_safety_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_13 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_14 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_15 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_16 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_17 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_18 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full data 2 output_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition pluck_safety_wit_19 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full data 2 (replace_Znth (0) ((Znth i input_l 0)) (output_l)) )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition pluck_safety_wit_20 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (((data + (0 * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data 1 2 )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition pluck_safety_wit_21 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (((data + (1 * sizeof(INT) ) )) # Int  |-> i)
  **  (((data + (0 * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition pluck_safety_wit_22 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full data 2 (replace_Znth (1) (i) ((replace_Znth (0) ((Znth i input_l 0)) (output_l)))) )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition pluck_safety_wit_23 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) >= (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full data 2 output_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pluck_safety_wit_24 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) <> 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pluck_safety_wit_25 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) <> 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pluck_safety_wit_26 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full data 2 (replace_Znth (1) (i) ((replace_Znth (0) ((Znth i input_l 0)) (output_l)))) )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pluck_safety_wit_27 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (((data + (1 * sizeof(INT) ) )) # Int  |-> i)
  **  (((data + (0 * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition pluck_entail_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l 0 output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full retval_2 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l 0 output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full retval_2 2 ))
  ||
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l 0 output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full retval_2 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l 0 output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full retval_2 2 ))
.

Definition pluck_entail_wit_2_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= 2) |] 
  &&  [| (output_size_2 = 0) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l_2 ) |] 
  &&  [| (output_size_2 = 0) |] 
  &&  [| (output_l_2 = nil) |]
  &&  (((data + (1 * sizeof(INT) ) )) # Int  |-> i)
  **  (((data + (0 * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
.

Definition pluck_entail_wit_2_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value_2: Z) (index_2: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) < (Znth 0 output_l_2 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= 2) |] 
  &&  [| (output_size_2 = 2) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l_2 ) |] 
  &&  [| (output_size_2 = 2) |] 
  &&  [| (output_l_2 = (cons (value_2) ((cons (index_2) (nil))))) |]
  &&  (IntArray.full data 2 (replace_Znth (1) (i) ((replace_Znth (0) ((Znth i input_l 0)) (output_l_2)))) )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
.

Definition pluck_entail_wit_2_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) <> 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= 2) |] 
  &&  [| (output_size_2 = 0) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l_2 ) |] 
  &&  [| (output_size_2 = 0) |] 
  &&  [| (output_l_2 = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
.

Definition pluck_entail_wit_2_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value_2: Z) (index_2: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) <> 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= 2) |] 
  &&  [| (output_size_2 = 2) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l_2 ) |] 
  &&  [| (output_size_2 = 2) |] 
  &&  [| (output_l_2 = (cons (value_2) ((cons (index_2) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l_2 )
|--
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
.

Definition pluck_entail_wit_2_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value_2: Z) (index_2: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) >= (Znth 0 output_l_2 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= 2) |] 
  &&  [| (output_size_2 = 2) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l_2 ) |] 
  &&  [| (output_size_2 = 2) |] 
  &&  [| (output_l_2 = (cons (value_2) ((cons (index_2) (nil))))) |]
  &&  (IntArray.full data 2 output_l_2 )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
  ||
  (EX (value: Z)  (index: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l ))
  ||
  (EX (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l (i + 1 ) output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 ))
.

Definition pluck_return_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data_2: Z) (out: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= 2) |] 
  &&  [| (output_size_2 = 0) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l_2 ) |] 
  &&  [| (output_size_2 = 0) |] 
  &&  [| (output_l_2 = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data_2 2 )
|--
  (EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_68_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 2 ))
  ||
  (EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_68_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 2 ))
.

Definition pluck_return_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data_2: Z) (out: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= 2) |] 
  &&  [| (output_size_2 = 2) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l_2 ) |] 
  &&  [| (output_size_2 = 2) |] 
  &&  [| (output_l_2 = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data_2 2 output_l_2 )
|--
  (EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_68_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 2 ))
  ||
  (EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_68_spec_z input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 2 ))
.

Definition pluck_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition pluck_partial_solve_wit_2_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |]
.

Definition pluck_partial_solve_wit_2_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_68_pre_z input_l ) |] 
  &&  [| (list_nonnegative input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (IntArray.full arr_pre arr_size_pre input_l )
.

Definition pluck_partial_solve_wit_2 := pluck_partial_solve_wit_2_pure -> pluck_partial_solve_wit_2_aux.

Definition pluck_partial_solve_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
.

Definition pluck_partial_solve_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
.

Definition pluck_partial_solve_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
.

Definition pluck_partial_solve_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (IntArray.full data 2 output_l )
|--
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (((data + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 output_l 0))
  **  (IntArray.missing_i data 0 0 2 output_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition pluck_partial_solve_wit_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
.

Definition pluck_partial_solve_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data 2 )
|--
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (((data + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data 1 2 )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition pluck_partial_solve_wit_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full data 2 output_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
  **  (IntArray.full data 2 output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition pluck_partial_solve_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  (IntArray.full data 2 output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (((data + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data 0 0 2 output_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition pluck_partial_solve_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (value: Z) (index: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (IntArray.full data 2 (replace_Znth (0) ((Znth i input_l 0)) (output_l)) )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| ((Znth i input_l 0) < (Znth 0 output_l 0)) |] 
  &&  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_l = (cons (value) ((cons (index) (nil))))) |]
  &&  (((data + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i data 1 0 2 (replace_Znth (0) ((Znth i input_l 0)) (output_l)) )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition pluck_partial_solve_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (((data + (0 * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data 1 2 )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (((Znth i input_l 0) % ( 2 ) ) = 0) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |] 
  &&  [| (arr_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 2) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (list_nonnegative input_l ) |] 
  &&  [| (pluck_loop_state input_l i output_l ) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_l = nil) |]
  &&  (((data + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((data + (0 * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_pluck_safety_wit_1 : pluck_safety_wit_1.
Axiom proof_of_pluck_safety_wit_2 : pluck_safety_wit_2.
Axiom proof_of_pluck_safety_wit_3 : pluck_safety_wit_3.
Axiom proof_of_pluck_safety_wit_4 : pluck_safety_wit_4.
Axiom proof_of_pluck_safety_wit_5 : pluck_safety_wit_5.
Axiom proof_of_pluck_safety_wit_6 : pluck_safety_wit_6.
Axiom proof_of_pluck_safety_wit_7 : pluck_safety_wit_7.
Axiom proof_of_pluck_safety_wit_8 : pluck_safety_wit_8.
Axiom proof_of_pluck_safety_wit_9 : pluck_safety_wit_9.
Axiom proof_of_pluck_safety_wit_10 : pluck_safety_wit_10.
Axiom proof_of_pluck_safety_wit_11 : pluck_safety_wit_11.
Axiom proof_of_pluck_safety_wit_12 : pluck_safety_wit_12.
Axiom proof_of_pluck_safety_wit_13 : pluck_safety_wit_13.
Axiom proof_of_pluck_safety_wit_14 : pluck_safety_wit_14.
Axiom proof_of_pluck_safety_wit_15 : pluck_safety_wit_15.
Axiom proof_of_pluck_safety_wit_16 : pluck_safety_wit_16.
Axiom proof_of_pluck_safety_wit_17 : pluck_safety_wit_17.
Axiom proof_of_pluck_safety_wit_18 : pluck_safety_wit_18.
Axiom proof_of_pluck_safety_wit_19 : pluck_safety_wit_19.
Axiom proof_of_pluck_safety_wit_20 : pluck_safety_wit_20.
Axiom proof_of_pluck_safety_wit_21 : pluck_safety_wit_21.
Axiom proof_of_pluck_safety_wit_22 : pluck_safety_wit_22.
Axiom proof_of_pluck_safety_wit_23 : pluck_safety_wit_23.
Axiom proof_of_pluck_safety_wit_24 : pluck_safety_wit_24.
Axiom proof_of_pluck_safety_wit_25 : pluck_safety_wit_25.
Axiom proof_of_pluck_safety_wit_26 : pluck_safety_wit_26.
Axiom proof_of_pluck_safety_wit_27 : pluck_safety_wit_27.
Axiom proof_of_pluck_entail_wit_1 : pluck_entail_wit_1.
Axiom proof_of_pluck_entail_wit_2_1 : pluck_entail_wit_2_1.
Axiom proof_of_pluck_entail_wit_2_2 : pluck_entail_wit_2_2.
Axiom proof_of_pluck_entail_wit_2_3 : pluck_entail_wit_2_3.
Axiom proof_of_pluck_entail_wit_2_4 : pluck_entail_wit_2_4.
Axiom proof_of_pluck_entail_wit_2_5 : pluck_entail_wit_2_5.
Axiom proof_of_pluck_return_wit_1 : pluck_return_wit_1.
Axiom proof_of_pluck_return_wit_2 : pluck_return_wit_2.
Axiom proof_of_pluck_partial_solve_wit_1 : pluck_partial_solve_wit_1.
Axiom proof_of_pluck_partial_solve_wit_2_pure : pluck_partial_solve_wit_2_pure.
Axiom proof_of_pluck_partial_solve_wit_2 : pluck_partial_solve_wit_2.
Axiom proof_of_pluck_partial_solve_wit_3 : pluck_partial_solve_wit_3.
Axiom proof_of_pluck_partial_solve_wit_4 : pluck_partial_solve_wit_4.
Axiom proof_of_pluck_partial_solve_wit_5 : pluck_partial_solve_wit_5.
Axiom proof_of_pluck_partial_solve_wit_6 : pluck_partial_solve_wit_6.
Axiom proof_of_pluck_partial_solve_wit_7 : pluck_partial_solve_wit_7.
Axiom proof_of_pluck_partial_solve_wit_8 : pluck_partial_solve_wit_8.
Axiom proof_of_pluck_partial_solve_wit_9 : pluck_partial_solve_wit_9.
Axiom proof_of_pluck_partial_solve_wit_10 : pluck_partial_solve_wit_10.
Axiom proof_of_pluck_partial_solve_wit_11 : pluck_partial_solve_wit_11.
Axiom proof_of_pluck_partial_solve_wit_12 : pluck_partial_solve_wit_12.

End VC_Correct.
