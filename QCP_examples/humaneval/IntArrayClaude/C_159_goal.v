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
Require Import coins_159.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function eat -----*)

Definition eat_safety_wit_1 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition eat_safety_wit_2 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition eat_safety_wit_3 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eat_safety_wit_4 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| False |]
.

Definition eat_safety_wit_5 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eat_safety_wit_6 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| ((number_pre + remaining_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (number_pre + remaining_pre )) |]
.

Definition eat_safety_wit_7 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + remaining_pre ))
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eat_safety_wit_8 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + remaining_pre ))
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eat_safety_wit_9 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition eat_safety_wit_10 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| ((number_pre + need_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (number_pre + need_pre )) |]
.

Definition eat_safety_wit_11 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + need_pre ))
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition eat_safety_wit_12 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + need_pre ))
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| ((remaining_pre - need_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (remaining_pre - need_pre )) |]
.

Definition eat_return_wit_1 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> (remaining_pre - need_pre ))
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + need_pre ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (retval <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_159_spec_z number_pre need_pre remaining_pre output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data output_size output_l )
.

Definition eat_return_wit_2 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> 0)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + remaining_pre ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (retval <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (output_size = 2) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_159_spec_z number_pre need_pre remaining_pre output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data output_size output_l )
.

Definition eat_partial_solve_wit_1 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) ,
  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  emp
|--
  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  emp
.

Definition eat_partial_solve_wit_2_pure := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "remaining" ) )) # Int  |-> remaining_pre)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "number" ) )) # Int  |-> number_pre)
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |]
.

Definition eat_partial_solve_wit_2_aux := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  [| (2 >= 0) |] 
  &&  [| (2 < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition eat_partial_solve_wit_2 := eat_partial_solve_wit_2_pure -> eat_partial_solve_wit_2_aux.

Definition eat_partial_solve_wit_3 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition eat_partial_solve_wit_4 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + remaining_pre ))
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (need_pre > remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + remaining_pre ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition eat_partial_solve_wit_5 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (IntArray.undef_full retval_2 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition eat_partial_solve_wit_6 := 
forall (remaining_pre: Z) (need_pre: Z) (number_pre: Z) (retval: Z) (retval_2: Z) ,
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + need_pre ))
  **  (IntArray.undef_seg retval_2 1 2 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  [| (need_pre <= remaining_pre) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (problem_159_pre_z number_pre need_pre remaining_pre ) |]
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> (number_pre + need_pre ))
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_eat_safety_wit_1 : eat_safety_wit_1.
Axiom proof_of_eat_safety_wit_2 : eat_safety_wit_2.
Axiom proof_of_eat_safety_wit_3 : eat_safety_wit_3.
Axiom proof_of_eat_safety_wit_4 : eat_safety_wit_4.
Axiom proof_of_eat_safety_wit_5 : eat_safety_wit_5.
Axiom proof_of_eat_safety_wit_6 : eat_safety_wit_6.
Axiom proof_of_eat_safety_wit_7 : eat_safety_wit_7.
Axiom proof_of_eat_safety_wit_8 : eat_safety_wit_8.
Axiom proof_of_eat_safety_wit_9 : eat_safety_wit_9.
Axiom proof_of_eat_safety_wit_10 : eat_safety_wit_10.
Axiom proof_of_eat_safety_wit_11 : eat_safety_wit_11.
Axiom proof_of_eat_safety_wit_12 : eat_safety_wit_12.
Axiom proof_of_eat_return_wit_1 : eat_return_wit_1.
Axiom proof_of_eat_return_wit_2 : eat_return_wit_2.
Axiom proof_of_eat_partial_solve_wit_1 : eat_partial_solve_wit_1.
Axiom proof_of_eat_partial_solve_wit_2_pure : eat_partial_solve_wit_2_pure.
Axiom proof_of_eat_partial_solve_wit_2 : eat_partial_solve_wit_2.
Axiom proof_of_eat_partial_solve_wit_3 : eat_partial_solve_wit_3.
Axiom proof_of_eat_partial_solve_wit_4 : eat_partial_solve_wit_4.
Axiom proof_of_eat_partial_solve_wit_5 : eat_partial_solve_wit_5.
Axiom proof_of_eat_partial_solve_wit_6 : eat_partial_solve_wit_6.

End VC_Correct.
