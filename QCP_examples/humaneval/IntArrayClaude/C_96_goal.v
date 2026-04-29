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
Require Import coins_96.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function count_up_to -----*)

Definition count_up_to_safety_wit_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_up_to_safety_wit_2 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_up_to_safety_wit_3 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition count_up_to_safety_wit_4 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (n_pre > 2) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition count_up_to_safety_wit_5 := 
forall (n_pre: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_up_to_safety_wit_6 := 
forall (n_pre: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_up_to_safety_wit_7 := 
forall (n_pre: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (output_size <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| False |]
.

Definition count_up_to_safety_wit_8 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = nil) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition count_up_to_safety_wit_9 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = nil) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_up_to_safety_wit_10 := 
forall (n_pre: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (output_size <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  ((( &( "isp" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_up_to_safety_wit_11 := 
forall (n_pre: Z) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (output_size <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  ((( &( "isp" ) )) # Int  |-> 1)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_up_to_safety_wit_12 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| ((i <> (INT_MIN)) \/ ((Znth (j - 0 ) output_l 0) <> (-1))) |] 
  &&  [| ((Znth (j - 0 ) output_l 0) <> 0) |]
.

Definition count_up_to_safety_wit_13 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (i: Z) (j: Z) (isp: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l) (0)) <= (i ÷ (Znth (j) (output_l) (0)) )) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| ((i <> (INT_MIN)) \/ ((Znth (j - 0 ) output_l 0) <> (-1))) |] 
  &&  [| ((Znth (j - 0 ) output_l 0) <> 0) |]
.

Definition count_up_to_safety_wit_14 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (i: Z) (j: Z) (isp: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l) (0)) <= (i ÷ (Znth (j) (output_l) (0)) )) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_up_to_safety_wit_15 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (i: Z) (j: Z) (isp: Z) ,
  [| ((i % ( (Znth (j - 0 ) output_l 0) ) ) = 0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l) (0)) <= (i ÷ (Znth (j) (output_l) (0)) )) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition count_up_to_safety_wit_16 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (i: Z) (j: Z) (isp: Z) ,
  [| ((i % ( (Znth (j - 0 ) output_l 0) ) ) <> 0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l) (0)) <= (i ÷ (Znth (j) (output_l) (0)) )) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition count_up_to_safety_wit_17 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (i: Z) (j: Z) (isp: Z) ,
  [| ((i % ( (Znth (j - 0 ) output_l 0) ) ) = 0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l) (0)) <= (i ÷ (Znth (j) (output_l) (0)) )) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| ((j + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (j + 1 )) |]
.

Definition count_up_to_safety_wit_18 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 0 ) output_l 0) > (i ÷ (Znth (j - 0 ) output_l 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition count_up_to_safety_wit_19 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 0 ) output_l 0) > (i ÷ (Znth (j - 0 ) output_l 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_up_to_safety_wit_20 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j >= output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition count_up_to_safety_wit_21 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j >= output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "isp" ) )) # Int  |-> isp)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition count_up_to_safety_wit_22 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j >= output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp = 0) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_up_to_safety_wit_23 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 0 ) output_l 0) > (i ÷ (Znth (j - 0 ) output_l 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp = 0) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_up_to_safety_wit_24 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j >= output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_up_to_safety_wit_25 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 0 ) output_l 0) > (i ÷ (Znth (j - 0 ) output_l 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_up_to_safety_wit_26 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = nil) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition count_up_to_entail_wit_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (n_pre > 2) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  (EX (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (Zlength (output_l))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 = 0) |] 
  &&  [| (count_up_to_state 2 output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 n_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (Zlength (output_l))) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (0 < 2) |] 
  &&  [| (count_up_to_state 2 output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 n_pre ))
.

Definition count_up_to_entail_wit_2_1 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (output_size = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (count_up_to_state i output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = nil) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_entail_wit_2_2 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (output_size = 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (count_up_to_state i output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = nil) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_entail_wit_3 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (output_size <> 0) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (count_up_to_state i output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (1 <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l 0 1 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_entail_wit_4 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l_2: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 0 ) output_l_2 0) <= (i ÷ (Znth (j - 0 ) output_l_2 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l_2 ) |] 
  &&  [| (prime_test_state i output_l_2 j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l) (0)) <= (i ÷ (Znth (j) (output_l) (0)) )) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_entail_wit_5_1 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (output_size: Z) (i: Z) (j: Z) (isp: Z) ,
  [| ((i % ( (Znth (j - 0 ) output_l_2 0) ) ) = 0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l_2) (0)) <= (i ÷ (Znth (j) (output_l_2) (0)) )) |] 
  &&  [| (count_up_to_state i output_l_2 ) |] 
  &&  [| (prime_test_state i output_l_2 j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= output_size) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l (j + 1 ) 0 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_entail_wit_5_2 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (output_size: Z) (i: Z) (j: Z) (isp: Z) ,
  [| ((i % ( (Znth (j - 0 ) output_l_2 0) ) ) <> 0) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l_2) (0)) <= (i ÷ (Znth (j) (output_l_2) (0)) )) |] 
  &&  [| (count_up_to_state i output_l_2 ) |] 
  &&  [| (prime_test_state i output_l_2 j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= (j + 1 )) |] 
  &&  [| ((j + 1 ) <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l (j + 1 ) isp ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_entail_wit_6_1 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (out: Z) (data: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_l_2 = nil) |] 
  &&  [| (count_up_to_state i output_l_2 ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
|--
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((output_size + 1 ) <= n_pre) |] 
  &&  [| ((output_size + 1 ) = 0) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((output_size + 1 ) <= n_pre) |] 
  &&  [| ((output_size + 1 ) < (i + 1 )) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre ))
.

Definition count_up_to_entail_wit_6_2 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l_2: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 0 ) output_l_2 0) > (i ÷ (Znth (j - 0 ) output_l_2 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l_2 ) |] 
  &&  [| (prime_test_state i output_l_2 j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((output_size + 1 ) <= n_pre) |] 
  &&  [| ((output_size + 1 ) = 0) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((output_size + 1 ) <= n_pre) |] 
  &&  [| ((output_size + 1 ) < (i + 1 )) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre ))
.

Definition count_up_to_entail_wit_6_3 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l_2: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j >= output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l_2 ) |] 
  &&  [| (prime_test_state i output_l_2 j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
|--
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((output_size + 1 ) <= n_pre) |] 
  &&  [| ((output_size + 1 ) = 0) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| ((output_size + 1 ) <= n_pre) |] 
  &&  [| ((output_size + 1 ) < (i + 1 )) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre ))
.

Definition count_up_to_entail_wit_6_4 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l_2: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 0 ) output_l_2 0) > (i ÷ (Znth (j - 0 ) output_l_2 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l_2 ) |] 
  &&  [| (prime_test_state i output_l_2 j isp ) |] 
  &&  [| (isp = 0) |]
  &&  (IntArray.seg data 0 output_size output_l_2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < (i + 1 )) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre ))
.

Definition count_up_to_entail_wit_6_5 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l_2: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j >= output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l_2 ) |] 
  &&  [| (prime_test_state i output_l_2 j isp ) |] 
  &&  [| (isp = 0) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre ))
  ||
  (EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < (i + 1 )) |] 
  &&  [| (count_up_to_state (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre ))
.

Definition count_up_to_return_wit_1 := 
forall (n_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (n_pre <= 2) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (retval <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (problem_96_spec_z n_pre output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_return_wit_2 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data_2: Z) (out: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_size_2 <= n_pre) |] 
  &&  [| (output_size_2 < i) |] 
  &&  [| (count_up_to_state i output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data_2 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data_2 output_size_2 n_pre )
|--
  EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (problem_96_spec_z n_pre output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_return_wit_3 := 
forall (n_pre: Z) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data_2: Z) (out: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (output_size_2 <= n_pre) |] 
  &&  [| (output_size_2 = 0) |] 
  &&  [| (count_up_to_state i output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.seg data_2 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data_2 output_size_2 n_pre )
|--
  EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (problem_96_spec_z n_pre output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_partial_solve_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  emp
|--
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  emp
.

Definition count_up_to_partial_solve_wit_2_pure := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (n_pre >= 0) |] 
  &&  [| (n_pre < INT_MAX) |]
.

Definition count_up_to_partial_solve_wit_2_aux := 
forall (n_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  [| (n_pre >= 0) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (problem_96_pre_z n_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition count_up_to_partial_solve_wit_2 := count_up_to_partial_solve_wit_2_pure -> count_up_to_partial_solve_wit_2_aux.

Definition count_up_to_partial_solve_wit_3 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (i: Z) (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = nil) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (output_size = 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_l = nil) |] 
  &&  [| (count_up_to_state i output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition count_up_to_partial_solve_wit_4 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (((data + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) output_l 0))
  **  (IntArray.missing_i data j 0 output_size output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_partial_solve_wit_5 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (((data + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) output_l 0))
  **  (IntArray.missing_i data j 0 output_size output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_partial_solve_wit_6 := 
forall (n_pre: Z) (output_l: (@list Z)) (out: Z) (data: Z) (output_size: Z) (i: Z) (j: Z) (isp: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l) (0)) <= (i ÷ (Znth (j) (output_l) (0)) )) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j < output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| ((Znth (j) (output_l) (0)) <= (i ÷ (Znth (j) (output_l) (0)) )) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |]
  &&  (((data + (j * sizeof(INT) ) )) # Int  |-> (Znth (j - 0 ) output_l 0))
  **  (IntArray.missing_i data j 0 output_size output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
.

Definition count_up_to_partial_solve_wit_7 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| (j >= output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| (j >= output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
.

Definition count_up_to_partial_solve_wit_8 := 
forall (n_pre: Z) (isp: Z) (j: Z) (i: Z) (output_l: (@list Z)) (output_size: Z) (data: Z) (out: Z) ,
  [| ((Znth (j - 0 ) output_l 0) > (i ÷ (Znth (j - 0 ) output_l 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size n_pre )
|--
  [| ((Znth (j - 0 ) output_l 0) > (i ÷ (Znth (j - 0 ) output_l 0) )) |] 
  &&  [| (j < output_size) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (2 < n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (output_size <= n_pre) |] 
  &&  [| (output_size < i) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (0 <= j) |] 
  &&  [| (j <= output_size) |] 
  &&  [| (0 <= isp) |] 
  &&  [| (isp <= 1) |] 
  &&  [| (count_up_to_state i output_l ) |] 
  &&  [| (prime_test_state i output_l j isp ) |] 
  &&  [| (isp <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) n_pre )
  **  (IntArray.seg data 0 output_size output_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_count_up_to_safety_wit_1 : count_up_to_safety_wit_1.
Axiom proof_of_count_up_to_safety_wit_2 : count_up_to_safety_wit_2.
Axiom proof_of_count_up_to_safety_wit_3 : count_up_to_safety_wit_3.
Axiom proof_of_count_up_to_safety_wit_4 : count_up_to_safety_wit_4.
Axiom proof_of_count_up_to_safety_wit_5 : count_up_to_safety_wit_5.
Axiom proof_of_count_up_to_safety_wit_6 : count_up_to_safety_wit_6.
Axiom proof_of_count_up_to_safety_wit_7 : count_up_to_safety_wit_7.
Axiom proof_of_count_up_to_safety_wit_8 : count_up_to_safety_wit_8.
Axiom proof_of_count_up_to_safety_wit_9 : count_up_to_safety_wit_9.
Axiom proof_of_count_up_to_safety_wit_10 : count_up_to_safety_wit_10.
Axiom proof_of_count_up_to_safety_wit_11 : count_up_to_safety_wit_11.
Axiom proof_of_count_up_to_safety_wit_12 : count_up_to_safety_wit_12.
Axiom proof_of_count_up_to_safety_wit_13 : count_up_to_safety_wit_13.
Axiom proof_of_count_up_to_safety_wit_14 : count_up_to_safety_wit_14.
Axiom proof_of_count_up_to_safety_wit_15 : count_up_to_safety_wit_15.
Axiom proof_of_count_up_to_safety_wit_16 : count_up_to_safety_wit_16.
Axiom proof_of_count_up_to_safety_wit_17 : count_up_to_safety_wit_17.
Axiom proof_of_count_up_to_safety_wit_18 : count_up_to_safety_wit_18.
Axiom proof_of_count_up_to_safety_wit_19 : count_up_to_safety_wit_19.
Axiom proof_of_count_up_to_safety_wit_20 : count_up_to_safety_wit_20.
Axiom proof_of_count_up_to_safety_wit_21 : count_up_to_safety_wit_21.
Axiom proof_of_count_up_to_safety_wit_22 : count_up_to_safety_wit_22.
Axiom proof_of_count_up_to_safety_wit_23 : count_up_to_safety_wit_23.
Axiom proof_of_count_up_to_safety_wit_24 : count_up_to_safety_wit_24.
Axiom proof_of_count_up_to_safety_wit_25 : count_up_to_safety_wit_25.
Axiom proof_of_count_up_to_safety_wit_26 : count_up_to_safety_wit_26.
Axiom proof_of_count_up_to_entail_wit_1 : count_up_to_entail_wit_1.
Axiom proof_of_count_up_to_entail_wit_2_1 : count_up_to_entail_wit_2_1.
Axiom proof_of_count_up_to_entail_wit_2_2 : count_up_to_entail_wit_2_2.
Axiom proof_of_count_up_to_entail_wit_3 : count_up_to_entail_wit_3.
Axiom proof_of_count_up_to_entail_wit_4 : count_up_to_entail_wit_4.
Axiom proof_of_count_up_to_entail_wit_5_1 : count_up_to_entail_wit_5_1.
Axiom proof_of_count_up_to_entail_wit_5_2 : count_up_to_entail_wit_5_2.
Axiom proof_of_count_up_to_entail_wit_6_1 : count_up_to_entail_wit_6_1.
Axiom proof_of_count_up_to_entail_wit_6_2 : count_up_to_entail_wit_6_2.
Axiom proof_of_count_up_to_entail_wit_6_3 : count_up_to_entail_wit_6_3.
Axiom proof_of_count_up_to_entail_wit_6_4 : count_up_to_entail_wit_6_4.
Axiom proof_of_count_up_to_entail_wit_6_5 : count_up_to_entail_wit_6_5.
Axiom proof_of_count_up_to_return_wit_1 : count_up_to_return_wit_1.
Axiom proof_of_count_up_to_return_wit_2 : count_up_to_return_wit_2.
Axiom proof_of_count_up_to_return_wit_3 : count_up_to_return_wit_3.
Axiom proof_of_count_up_to_partial_solve_wit_1 : count_up_to_partial_solve_wit_1.
Axiom proof_of_count_up_to_partial_solve_wit_2_pure : count_up_to_partial_solve_wit_2_pure.
Axiom proof_of_count_up_to_partial_solve_wit_2 : count_up_to_partial_solve_wit_2.
Axiom proof_of_count_up_to_partial_solve_wit_3 : count_up_to_partial_solve_wit_3.
Axiom proof_of_count_up_to_partial_solve_wit_4 : count_up_to_partial_solve_wit_4.
Axiom proof_of_count_up_to_partial_solve_wit_5 : count_up_to_partial_solve_wit_5.
Axiom proof_of_count_up_to_partial_solve_wit_6 : count_up_to_partial_solve_wit_6.
Axiom proof_of_count_up_to_partial_solve_wit_7 : count_up_to_partial_solve_wit_7.
Axiom proof_of_count_up_to_partial_solve_wit_8 : count_up_to_partial_solve_wit_8.

End VC_Correct.
