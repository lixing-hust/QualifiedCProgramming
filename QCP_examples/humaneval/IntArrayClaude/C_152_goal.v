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
Require Import coins_152.
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

(*----- Function compare -----*)

Definition compare_safety_wit_1 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (retval: Z) ,
  [| (game_size_pre < guess_size_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "guess_size" ) )) # Int  |-> guess_size_pre)
  **  ((( &( "guess" ) )) # Ptr  |-> guess_pre)
  **  ((( &( "game_size" ) )) # Int  |-> game_size_pre)
  **  ((( &( "game" ) )) # Ptr  |-> game_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
|--
  [| False |]
.

Definition compare_safety_wit_2 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (game_size_pre >= guess_size_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 guess_size_pre )
  **  ((( &( "n" ) )) # Int  |-> guess_size_pre)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> guess_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "guess_size" ) )) # Int  |-> guess_size_pre)
  **  ((( &( "guess" ) )) # Ptr  |-> guess_pre)
  **  ((( &( "game_size" ) )) # Int  |-> game_size_pre)
  **  ((( &( "game" ) )) # Ptr  |-> game_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition compare_safety_wit_3 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (game_size_pre >= guess_size_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 guess_size_pre )
  **  ((( &( "n" ) )) # Int  |-> guess_size_pre)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> guess_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "guess_size" ) )) # Int  |-> guess_size_pre)
  **  ((( &( "guess" ) )) # Ptr  |-> guess_pre)
  **  ((( &( "game_size" ) )) # Int  |-> game_size_pre)
  **  ((( &( "game" ) )) # Ptr  |-> game_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
|--
  [| False |]
.

Definition compare_safety_wit_4 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (game_size_pre >= guess_size_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 guess_size_pre )
  **  ((( &( "n" ) )) # Int  |-> guess_size_pre)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> guess_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "guess_size" ) )) # Int  |-> guess_size_pre)
  **  ((( &( "guess" ) )) # Ptr  |-> guess_pre)
  **  ((( &( "game_size" ) )) # Int  |-> game_size_pre)
  **  ((( &( "game" ) )) # Ptr  |-> game_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition compare_safety_wit_5 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.full game_pre game_size_pre game_l )
  **  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "diff" ) )) # Int  |->_)
  **  ((( &( "game" ) )) # Ptr  |-> game_pre)
  **  ((( &( "guess" ) )) # Ptr  |-> guess_pre)
  **  ((( &( "game_size" ) )) # Int  |-> game_size_pre)
  **  ((( &( "guess_size" ) )) # Int  |-> guess_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
|--
  [| (((Znth i game_l 0) - (Znth i guess_l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth i game_l 0) - (Znth i guess_l 0) )) |]
.

Definition compare_safety_wit_6 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l: (@list Z)) (out: Z) (data: Z) (n: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l))) |] 
  &&  [| (compare_prefix (i + 1 ) game_l guess_l output_l ) |]
  &&  ((( &( "game" ) )) # Ptr  |-> game_pre)
  **  ((( &( "guess" ) )) # Ptr  |-> guess_pre)
  **  ((( &( "game_size" ) )) # Int  |-> game_size_pre)
  **  ((( &( "guess_size" ) )) # Int  |-> guess_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) n )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition compare_entail_wit_1 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (game_size_pre >= guess_size_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  (IntArray.undef_full retval_2 guess_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> guess_size_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
|--
  EX (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (guess_size_pre = game_size_pre) |] 
  &&  [| (guess_size_pre = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (0 = (Zlength (output_l))) |] 
  &&  [| (compare_prefix 0 game_l guess_l output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> guess_size_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 guess_size_pre )
.

Definition compare_entail_wit_2 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = (Zabs (((Znth i game_l 0) - (Znth i guess_l 0) )))) |] 
  &&  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l_2))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l_2 ) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |-> retval)
  **  (IntArray.undef_seg data (i + 1 ) n )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.full game_pre game_size_pre game_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.seg data 0 i output_l_2 )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l))) |] 
  &&  [| (compare_prefix (i + 1 ) game_l guess_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) n )
.

Definition compare_entail_wit_3 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l_2: (@list Z)) (out: Z) (data: Z) (n: Z) (i: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i < n) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l_2))) |] 
  &&  [| (compare_prefix (i + 1 ) game_l guess_l output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l_2 )
  **  (IntArray.undef_seg data (i + 1 ) n )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n) |] 
  &&  [| ((i + 1 ) = (Zlength (output_l))) |] 
  &&  [| (compare_prefix (i + 1 ) game_l guess_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg data 0 (i + 1 ) output_l )
  **  (IntArray.undef_seg data (i + 1 ) n )
.

Definition compare_return_wit_1 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l_2: (@list Z)) (i: Z) (n: Z) (data_2: Z) (out: Z) ,
  [| (i >= n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l_2))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg data_2 0 i output_l_2 )
  **  (IntArray.undef_seg data_2 i n )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (output_size = game_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_152_spec_z game_l guess_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.full data output_size output_l )
.

Definition compare_partial_solve_wit_1 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) ,
  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
|--
  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
.

Definition compare_partial_solve_wit_2_pure := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (retval: Z) ,
  [| (game_size_pre >= guess_size_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  ((( &( "n" ) )) # Int  |-> guess_size_pre)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> guess_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "guess_size" ) )) # Int  |-> guess_size_pre)
  **  ((( &( "guess" ) )) # Ptr  |-> guess_pre)
  **  ((( &( "game_size" ) )) # Int  |-> game_size_pre)
  **  ((( &( "game" ) )) # Ptr  |-> game_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
|--
  [| (guess_size_pre >= 0) |] 
  &&  [| (guess_size_pre < INT_MAX) |]
.

Definition compare_partial_solve_wit_2_aux := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (retval: Z) ,
  [| (game_size_pre >= guess_size_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> guess_size_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
|--
  [| (guess_size_pre >= 0) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre >= guess_size_pre) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> guess_size_pre)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
.

Definition compare_partial_solve_wit_2 := compare_partial_solve_wit_2_pure -> compare_partial_solve_wit_2_aux.

Definition compare_partial_solve_wit_3 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.full game_pre game_size_pre game_l )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
|--
  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (((game_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i game_l 0))
  **  (IntArray.missing_i game_pre i 0 game_size_pre game_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
.

Definition compare_partial_solve_wit_4 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (IntArray.full game_pre game_size_pre game_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
|--
  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (((guess_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i guess_l 0))
  **  (IntArray.missing_i guess_pre i 0 guess_size_pre guess_l )
  **  (IntArray.full game_pre game_size_pre game_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
.

Definition compare_partial_solve_wit_5_pure := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.full game_pre game_size_pre game_l )
  **  ((( &( "value" ) )) # Int  |->_)
  **  ((( &( "diff" ) )) # Int  |-> ((Znth i game_l 0) - (Znth i guess_l 0) ))
  **  ((( &( "game" ) )) # Ptr  |-> game_pre)
  **  ((( &( "guess" ) )) # Ptr  |-> guess_pre)
  **  ((( &( "game_size" ) )) # Int  |-> game_size_pre)
  **  ((( &( "guess_size" ) )) # Int  |-> guess_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
|--
  [| (((Znth i game_l 0) - (Znth i guess_l 0) ) <= INT_MAX) |] 
  &&  [| (INT_MIN < ((Znth i game_l 0) - (Znth i guess_l 0) )) |]
.

Definition compare_partial_solve_wit_5_aux := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (data: Z) (out: Z) ,
  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.full game_pre game_size_pre game_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
|--
  [| (((Znth i game_l 0) - (Znth i guess_l 0) ) <= INT_MAX) |] 
  &&  [| (INT_MIN < ((Znth i game_l 0) - (Znth i guess_l 0) )) |] 
  &&  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.full game_pre game_size_pre game_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
.

Definition compare_partial_solve_wit_5 := compare_partial_solve_wit_5_pure -> compare_partial_solve_wit_5_aux.

Definition compare_partial_solve_wit_6 := 
forall (guess_size_pre: Z) (guess_pre: Z) (game_size_pre: Z) (game_pre: Z) (guess_l: (@list Z)) (game_l: (@list Z)) (output_l: (@list Z)) (i: Z) (n: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = (Zabs (((Znth i game_l 0) - (Znth i guess_l 0) )))) |] 
  &&  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.full game_pre game_size_pre game_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.seg data 0 i output_l )
  **  (IntArray.undef_seg data i n )
|--
  [| (retval = (Zabs (((Znth i game_l 0) - (Znth i guess_l 0) )))) |] 
  &&  [| (i < n) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (n = game_size_pre) |] 
  &&  [| (n = guess_size_pre) |] 
  &&  [| (0 <= game_size_pre) |] 
  &&  [| (game_size_pre < INT_MAX) |] 
  &&  [| (0 <= guess_size_pre) |] 
  &&  [| (guess_size_pre < INT_MAX) |] 
  &&  [| (game_size_pre = (Zlength (game_l))) |] 
  &&  [| (guess_size_pre = (Zlength (guess_l))) |] 
  &&  [| (game_size_pre = guess_size_pre) |] 
  &&  [| (problem_152_pre_z game_l guess_l ) |] 
  &&  [| (compare_int_range game_l guess_l ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n) |] 
  &&  [| (i = (Zlength (output_l))) |] 
  &&  [| (compare_prefix i game_l guess_l output_l ) |]
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) n )
  **  (IntArray.full guess_pre guess_size_pre guess_l )
  **  (IntArray.full game_pre game_size_pre game_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> n)
  **  (IntArray.seg data 0 i output_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_compare_safety_wit_1 : compare_safety_wit_1.
Axiom proof_of_compare_safety_wit_2 : compare_safety_wit_2.
Axiom proof_of_compare_safety_wit_3 : compare_safety_wit_3.
Axiom proof_of_compare_safety_wit_4 : compare_safety_wit_4.
Axiom proof_of_compare_safety_wit_5 : compare_safety_wit_5.
Axiom proof_of_compare_safety_wit_6 : compare_safety_wit_6.
Axiom proof_of_compare_entail_wit_1 : compare_entail_wit_1.
Axiom proof_of_compare_entail_wit_2 : compare_entail_wit_2.
Axiom proof_of_compare_entail_wit_3 : compare_entail_wit_3.
Axiom proof_of_compare_return_wit_1 : compare_return_wit_1.
Axiom proof_of_compare_partial_solve_wit_1 : compare_partial_solve_wit_1.
Axiom proof_of_compare_partial_solve_wit_2_pure : compare_partial_solve_wit_2_pure.
Axiom proof_of_compare_partial_solve_wit_2 : compare_partial_solve_wit_2.
Axiom proof_of_compare_partial_solve_wit_3 : compare_partial_solve_wit_3.
Axiom proof_of_compare_partial_solve_wit_4 : compare_partial_solve_wit_4.
Axiom proof_of_compare_partial_solve_wit_5_pure : compare_partial_solve_wit_5_pure.
Axiom proof_of_compare_partial_solve_wit_5 : compare_partial_solve_wit_5.
Axiom proof_of_compare_partial_solve_wit_6 : compare_partial_solve_wit_6.

End VC_Correct.
