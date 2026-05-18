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
Require Import coins_163.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function generate_integers -----*)

Definition generate_integers_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) ,
  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "m" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_integers_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_integers_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_integers_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) ,
  [| (b_pre >= a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "capacity" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition generate_integers_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) ,
  [| (b_pre < a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "capacity" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> a_pre)
  **  ((( &( "a" ) )) # Int  |-> b_pre)
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition generate_integers_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (b_pre < a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 10 )
  **  ((( &( "capacity" ) )) # Int  |-> 10)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> a_pre)
  **  ((( &( "a" ) )) # Int  |-> b_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_integers_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (b_pre >= a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 10 )
  **  ((( &( "capacity" ) )) # Int  |-> 10)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_integers_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (b_pre < a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 10 )
  **  ((( &( "capacity" ) )) # Int  |-> 10)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> a_pre)
  **  ((( &( "a" ) )) # Int  |-> b_pre)
|--
  [| False |]
.

Definition generate_integers_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (b_pre >= a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 10 )
  **  ((( &( "capacity" ) )) # Int  |-> 10)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| False |]
.

Definition generate_integers_safety_wit_10 := 
forall (b0: Z) (a0: Z) (m_addr_v: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (capacity: Z) (a: Z) (b: Z) (data: Z) (out: Z) ,
  [| (i <= b) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (generate_prefix a i b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "capacity" ) )) # Int  |-> capacity)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size capacity )
|--
  [| (10 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 10) |]
.

Definition generate_integers_safety_wit_11 := 
forall (b0: Z) (a0: Z) (m_addr_v: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (capacity: Z) (a: Z) (b: Z) (data: Z) (out: Z) ,
  [| (i < 10) |] 
  &&  [| (i <= b) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (generate_prefix a i b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "capacity" ) )) # Int  |-> capacity)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size capacity )
|--
  [| ((i <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition generate_integers_safety_wit_12 := 
forall (b0: Z) (a0: Z) (m_addr_v: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (capacity: Z) (a: Z) (b: Z) (data: Z) (out: Z) ,
  [| (i < 10) |] 
  &&  [| (i <= b) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (generate_prefix a i b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "capacity" ) )) # Int  |-> capacity)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size capacity )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition generate_integers_safety_wit_13 := 
forall (b0: Z) (a0: Z) (m_addr_v: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (capacity: Z) (a: Z) (b: Z) (data: Z) (out: Z) ,
  [| (i < 10) |] 
  &&  [| (i <= b) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (generate_prefix a i b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "capacity" ) )) # Int  |-> capacity)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size capacity )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition generate_integers_safety_wit_14 := 
forall (b0: Z) (a0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (b: Z) (a: Z) (capacity: Z) (i: Z) (output_size: Z) (m_addr_v: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (i < 10) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= i) |] 
  &&  [| (i <= INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (output_size < 10) |] 
  &&  [| (generate_prefix a i b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) 10 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "capacity" ) )) # Int  |-> capacity)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition generate_integers_safety_wit_15 := 
forall (b0: Z) (a0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (b: Z) (a: Z) (capacity: Z) (i: Z) (output_size: Z) (m_addr_v: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= ((i + 1 ) - a )) |] 
  &&  [| (generate_prefix a (i + 1 ) b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "capacity" ) )) # Int  |-> capacity)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "m" ) )) # Int  |-> m_addr_v)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 10 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition generate_integers_entail_wit_1_1 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (b_pre >= a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  (IntArray.undef_full retval_2 10 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a_pre b_pre ) |] 
  &&  [| (10 = 10) |] 
  &&  [| (a_pre <= a_pre) |] 
  &&  [| (a_pre <= (b_pre + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (a_pre - a_pre )) |] 
  &&  [| (generate_prefix a_pre a_pre b_pre output_l ) |] 
  &&  [| (0 = (Zlength (output_l))) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 10 )
.

Definition generate_integers_entail_wit_1_2 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (b_pre < a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  (IntArray.undef_full retval_2 10 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 b_pre a_pre ) |] 
  &&  [| (10 = 10) |] 
  &&  [| (b_pre <= b_pre) |] 
  &&  [| (b_pre <= (a_pre + 1 )) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= (b_pre - b_pre )) |] 
  &&  [| (generate_prefix b_pre b_pre a_pre output_l ) |] 
  &&  [| (0 = (Zlength (output_l))) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 10 )
.

Definition generate_integers_entail_wit_2 := 
forall (b0: Z) (a0: Z) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (capacity: Z) (a: Z) (b: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (i < 10) |] 
  &&  [| (i <= b) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (generate_prefix a i b output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size capacity )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (i < 10) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= i) |] 
  &&  [| (i <= INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (output_size < 10) |] 
  &&  [| (generate_prefix a i b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 10 )
.

Definition generate_integers_entail_wit_3 := 
forall (b0: Z) (a0: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (b: Z) (a: Z) (capacity: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (i < 10) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= i) |] 
  &&  [| (i <= INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (output_size < 10) |] 
  &&  [| (generate_prefix a i b output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) 10 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (i < 10) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) <= ((i + 1 ) - a )) |] 
  &&  [| (generate_prefix a (i + 1 ) b output_l ) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) 10 )
.

Definition generate_integers_entail_wit_4_1 := 
forall (b0: Z) (a0: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (b: Z) (a: Z) (capacity: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (i < 10) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= ((i + 1 ) - a )) |] 
  &&  [| (generate_prefix a (i + 1 ) b output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size 10 )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= ((i + 1 ) - a )) |] 
  &&  [| (generate_prefix a (i + 1 ) b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 10 )
.

Definition generate_integers_entail_wit_4_2 := 
forall (b0: Z) (a0: Z) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (capacity: Z) (a: Z) (b: Z) (data: Z) (out: Z) ,
  [| (i >= 10) |] 
  &&  [| (i <= b) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (generate_prefix a i b output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size capacity )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= ((i + 1 ) - a )) |] 
  &&  [| (generate_prefix a (i + 1 ) b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 10 )
.

Definition generate_integers_entail_wit_4_3 := 
forall (b0: Z) (a0: Z) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (capacity: Z) (a: Z) (b: Z) (data: Z) (out: Z) ,
  [| ((i % ( 2 ) ) <> 0) |] 
  &&  [| (i < 10) |] 
  &&  [| (i <= b) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (generate_prefix a i b output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size capacity )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= ((i + 1 ) - a )) |] 
  &&  [| (generate_prefix a (i + 1 ) b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 10 )
.

Definition generate_integers_entail_wit_5 := 
forall (b0: Z) (a0: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (b: Z) (a: Z) (capacity: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= ((i + 1 ) - a )) |] 
  &&  [| (generate_prefix a (i + 1 ) b output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size 10 )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= ((i + 1 ) - a )) |] 
  &&  [| (generate_prefix a (i + 1 ) b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size capacity )
.

Definition generate_integers_entail_wit_6 := 
forall (b0: Z) (a0: Z) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (capacity: Z) (a: Z) (b: Z) (data: Z) (out: Z) ,
  [| (i > b) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (generate_prefix a i b output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size capacity )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (i = (b + 1 )) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= 10) |] 
  &&  [| (generate_prefix a (b + 1 ) b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 10 )
.

Definition generate_integers_return_wit_1 := 
forall (b0: Z) (a0: Z) (output_l_2: (@list Z)) (out: Z) (data_2: Z) (b: Z) (a: Z) (capacity_2: Z) (i: Z) (output_size_2: Z) ,
  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity_2 = 10) |] 
  &&  [| (i = (b + 1 )) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= 10) |] 
  &&  [| (generate_prefix a (b + 1 ) b output_l_2 ) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data_2 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data_2 output_size_2 10 )
|--
  EX (output_l: (@list Z))  (capacity: Z)  (output_size: Z)  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= capacity) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (problem_163_spec_z a0 b0 output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 10 )
.

Definition generate_integers_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) ,
  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  emp
|--
  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  emp
.

Definition generate_integers_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) ,
  [| (b_pre < a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "capacity" ) )) # Int  |-> 10)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> a_pre)
  **  ((( &( "a" ) )) # Int  |-> b_pre)
|--
  [| (10 >= 0) |] 
  &&  [| (10 < INT_MAX) |]
.

Definition generate_integers_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) ,
  [| (b_pre < a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (10 >= 0) |] 
  &&  [| (10 < INT_MAX) |] 
  &&  [| (b_pre < a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition generate_integers_partial_solve_wit_2 := generate_integers_partial_solve_wit_2_pure -> generate_integers_partial_solve_wit_2_aux.

Definition generate_integers_partial_solve_wit_3_pure := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) ,
  [| (b_pre >= a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((( &( "capacity" ) )) # Int  |-> 10)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "m" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  [| (10 >= 0) |] 
  &&  [| (10 < INT_MAX) |]
.

Definition generate_integers_partial_solve_wit_3_aux := 
forall (b_pre: Z) (a_pre: Z) (b0: Z) (a0: Z) (retval: Z) ,
  [| (b_pre >= a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (10 >= 0) |] 
  &&  [| (10 < INT_MAX) |] 
  &&  [| (b_pre >= a_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (a_pre = a0) |] 
  &&  [| (b_pre = b0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition generate_integers_partial_solve_wit_3 := generate_integers_partial_solve_wit_3_pure -> generate_integers_partial_solve_wit_3_aux.

Definition generate_integers_partial_solve_wit_4 := 
forall (b0: Z) (a0: Z) (output_l: (@list Z)) (out: Z) (data: Z) (b: Z) (a: Z) (capacity: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (i < 10) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= i) |] 
  &&  [| (i <= INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (output_size < 10) |] 
  &&  [| (generate_prefix a i b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size 10 )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (problem_163_pre_z a0 b0 ) |] 
  &&  [| (0 < a0) |] 
  &&  [| (a0 < INT_MAX) |] 
  &&  [| (0 < b0) |] 
  &&  [| (b0 < INT_MAX) |] 
  &&  [| (generate_bounds a0 b0 a b ) |] 
  &&  [| (capacity = 10) |] 
  &&  [| (a <= i) |] 
  &&  [| (i <= b) |] 
  &&  [| (i < 10) |] 
  &&  [| ((i % ( 2 ) ) = 0) |] 
  &&  [| (INT_MIN <= i) |] 
  &&  [| (i <= INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i - a )) |] 
  &&  [| (output_size < 10) |] 
  &&  [| (generate_prefix a i b output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) 10 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_generate_integers_safety_wit_1 : generate_integers_safety_wit_1.
Axiom proof_of_generate_integers_safety_wit_2 : generate_integers_safety_wit_2.
Axiom proof_of_generate_integers_safety_wit_3 : generate_integers_safety_wit_3.
Axiom proof_of_generate_integers_safety_wit_4 : generate_integers_safety_wit_4.
Axiom proof_of_generate_integers_safety_wit_5 : generate_integers_safety_wit_5.
Axiom proof_of_generate_integers_safety_wit_6 : generate_integers_safety_wit_6.
Axiom proof_of_generate_integers_safety_wit_7 : generate_integers_safety_wit_7.
Axiom proof_of_generate_integers_safety_wit_8 : generate_integers_safety_wit_8.
Axiom proof_of_generate_integers_safety_wit_9 : generate_integers_safety_wit_9.
Axiom proof_of_generate_integers_safety_wit_10 : generate_integers_safety_wit_10.
Axiom proof_of_generate_integers_safety_wit_11 : generate_integers_safety_wit_11.
Axiom proof_of_generate_integers_safety_wit_12 : generate_integers_safety_wit_12.
Axiom proof_of_generate_integers_safety_wit_13 : generate_integers_safety_wit_13.
Axiom proof_of_generate_integers_safety_wit_14 : generate_integers_safety_wit_14.
Axiom proof_of_generate_integers_safety_wit_15 : generate_integers_safety_wit_15.
Axiom proof_of_generate_integers_entail_wit_1_1 : generate_integers_entail_wit_1_1.
Axiom proof_of_generate_integers_entail_wit_1_2 : generate_integers_entail_wit_1_2.
Axiom proof_of_generate_integers_entail_wit_2 : generate_integers_entail_wit_2.
Axiom proof_of_generate_integers_entail_wit_3 : generate_integers_entail_wit_3.
Axiom proof_of_generate_integers_entail_wit_4_1 : generate_integers_entail_wit_4_1.
Axiom proof_of_generate_integers_entail_wit_4_2 : generate_integers_entail_wit_4_2.
Axiom proof_of_generate_integers_entail_wit_4_3 : generate_integers_entail_wit_4_3.
Axiom proof_of_generate_integers_entail_wit_5 : generate_integers_entail_wit_5.
Axiom proof_of_generate_integers_entail_wit_6 : generate_integers_entail_wit_6.
Axiom proof_of_generate_integers_return_wit_1 : generate_integers_return_wit_1.
Axiom proof_of_generate_integers_partial_solve_wit_1 : generate_integers_partial_solve_wit_1.
Axiom proof_of_generate_integers_partial_solve_wit_2_pure : generate_integers_partial_solve_wit_2_pure.
Axiom proof_of_generate_integers_partial_solve_wit_2 : generate_integers_partial_solve_wit_2.
Axiom proof_of_generate_integers_partial_solve_wit_3_pure : generate_integers_partial_solve_wit_3_pure.
Axiom proof_of_generate_integers_partial_solve_wit_3 : generate_integers_partial_solve_wit_3.
Axiom proof_of_generate_integers_partial_solve_wit_4 : generate_integers_partial_solve_wit_4.

End VC_Correct.
