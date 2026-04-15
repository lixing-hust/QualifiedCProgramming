Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_25.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function factorize -----*)

Definition factorize_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_25_pre_z n0 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition factorize_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_25_pre_z n0 ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
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

Definition factorize_safety_wit_3 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
|--
  [| ((n <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition factorize_safety_wit_4 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
|--
  [| ((n <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition factorize_safety_wit_5 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition factorize_safety_wit_6 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
|--
  [| ((n <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition factorize_safety_wit_7 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> (n ÷ i ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
|--
  [| ((size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (size + 1 )) |]
.

Definition factorize_safety_wit_8 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> (n ÷ i ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition factorize_safety_wit_9 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> (n ÷ i ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (size + 1 ))
  **  (IntArray.seg data 0 size factors )
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition factorize_safety_wit_10 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> (n ÷ i ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (size + 1 ))
  **  (IntArray.seg data 0 size factors )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition factorize_safety_wit_11 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) <> 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition factorize_safety_wit_12 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> (n ÷ i ))
  **  ((( &( "i" ) )) # Int  |-> (i - 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (size + 1 ))
  **  (IntArray.seg data 0 size factors )
|--
  [| (((i - 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((i - 1 ) + 1 )) |]
.

Definition factorize_safety_wit_13 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i > (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |-> n)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
|--
  [| ((size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (size + 1 )) |]
.

Definition factorize_safety_wit_14 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i > (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |-> n)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition factorize_entail_wit_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_25_pre_z n0 ) |]
  &&  (IntArray.undef_full retval_2 n_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (factors: (@list Z))  (size: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n_pre) |] 
  &&  [| (n_pre <= n0) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n_pre ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n_pre 2 factors ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg retval_2 0 size factors )
  **  (IntArray.undef_seg retval_2 size n0 )
.

Definition factorize_entail_wit_2_1 := 
forall (n0: Z) (factors_2: (@list Z)) (size_2: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size_2) |] 
  &&  [| (size_2 < n0) |] 
  &&  [| (size_2 = (Zlength (factors_2))) |] 
  &&  [| ((size_2 + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors_2 ) |]
  &&  (((data + (size_2 * sizeof(INT) ) )) # Int  |-> i)
  **  (IntArray.undef_seg data (size_2 + 1 ) n0 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (size_2 + 1 ))
  **  (IntArray.seg data 0 size_2 factors_2 )
|--
  EX (factors: (@list Z))  (size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= (n ÷ i )) |] 
  &&  [| ((n ÷ i ) <= n0) |] 
  &&  [| (2 <= ((i - 1 ) + 1 )) |] 
  &&  [| (((i - 1 ) + 1 ) <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + (n ÷ i ) ) <= n0) |] 
  &&  [| (factorize_loop_state n0 (n ÷ i ) ((i - 1 ) + 1 ) factors ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
.

Definition factorize_entail_wit_2_2 := 
forall (n0: Z) (factors_2: (@list Z)) (size_2: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) <> 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size_2) |] 
  &&  [| (size_2 < n0) |] 
  &&  [| (size_2 = (Zlength (factors_2))) |] 
  &&  [| ((size_2 + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size_2)
  **  (IntArray.seg data 0 size_2 factors_2 )
  **  (IntArray.undef_seg data size_2 n0 )
|--
  EX (factors: (@list Z))  (size: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n (i + 1 ) factors ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
.

Definition factorize_return_wit_1 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data_2: Z) (out: Z) ,
  [| (i > (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data_2 + (size * sizeof(INT) ) )) # Int  |-> n)
  **  (IntArray.undef_seg data_2 (size + 1 ) n0 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (size + 1 ))
  **  (IntArray.seg data_2 0 size factors )
|--
  EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= n0) |] 
  &&  [| (problem_25_spec_z n0 output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size n0 )
.

Definition factorize_partial_solve_wit_1 := 
forall (n_pre: Z) (n0: Z) ,
  [| (n_pre = n0) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_25_pre_z n0 ) |]
  &&  emp
|--
  [| (n_pre = n0) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_25_pre_z n0 ) |]
  &&  emp
.

Definition factorize_partial_solve_wit_2_pure := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_25_pre_z n0 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (n_pre >= 0) |] 
  &&  [| (n_pre < INT_MAX) |]
.

Definition factorize_partial_solve_wit_2_aux := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_25_pre_z n0 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (n_pre >= 0) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (n_pre = n0) |] 
  &&  [| (2 <= n0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (problem_25_pre_z n0 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition factorize_partial_solve_wit_2 := factorize_partial_solve_wit_2_pure -> factorize_partial_solve_wit_2_aux.

Definition factorize_partial_solve_wit_3 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
|--
  [| ((n % ( i ) ) = 0) |] 
  &&  [| (i <= (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
.

Definition factorize_partial_solve_wit_4 := 
forall (n0: Z) (factors: (@list Z)) (size: Z) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i > (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
  **  (IntArray.undef_seg data size n0 )
|--
  [| (i > (n ÷ i )) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n0 < INT_MAX) |] 
  &&  [| (2 <= n) |] 
  &&  [| (n <= n0) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= n0) |] 
  &&  [| (0 <= size) |] 
  &&  [| (size < n0) |] 
  &&  [| (size = (Zlength (factors))) |] 
  &&  [| ((size + n ) <= n0) |] 
  &&  [| (factorize_loop_state n0 n i factors ) |]
  &&  (((data + (size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (size + 1 ) n0 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size factors )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_factorize_safety_wit_1 : factorize_safety_wit_1.
Axiom proof_of_factorize_safety_wit_2 : factorize_safety_wit_2.
Axiom proof_of_factorize_safety_wit_3 : factorize_safety_wit_3.
Axiom proof_of_factorize_safety_wit_4 : factorize_safety_wit_4.
Axiom proof_of_factorize_safety_wit_5 : factorize_safety_wit_5.
Axiom proof_of_factorize_safety_wit_6 : factorize_safety_wit_6.
Axiom proof_of_factorize_safety_wit_7 : factorize_safety_wit_7.
Axiom proof_of_factorize_safety_wit_8 : factorize_safety_wit_8.
Axiom proof_of_factorize_safety_wit_9 : factorize_safety_wit_9.
Axiom proof_of_factorize_safety_wit_10 : factorize_safety_wit_10.
Axiom proof_of_factorize_safety_wit_11 : factorize_safety_wit_11.
Axiom proof_of_factorize_safety_wit_12 : factorize_safety_wit_12.
Axiom proof_of_factorize_safety_wit_13 : factorize_safety_wit_13.
Axiom proof_of_factorize_safety_wit_14 : factorize_safety_wit_14.
Axiom proof_of_factorize_entail_wit_1 : factorize_entail_wit_1.
Axiom proof_of_factorize_entail_wit_2_1 : factorize_entail_wit_2_1.
Axiom proof_of_factorize_entail_wit_2_2 : factorize_entail_wit_2_2.
Axiom proof_of_factorize_return_wit_1 : factorize_return_wit_1.
Axiom proof_of_factorize_partial_solve_wit_1 : factorize_partial_solve_wit_1.
Axiom proof_of_factorize_partial_solve_wit_2_pure : factorize_partial_solve_wit_2_pure.
Axiom proof_of_factorize_partial_solve_wit_2 : factorize_partial_solve_wit_2.
Axiom proof_of_factorize_partial_solve_wit_3 : factorize_partial_solve_wit_3.
Axiom proof_of_factorize_partial_solve_wit_4 : factorize_partial_solve_wit_4.

End VC_Correct.
