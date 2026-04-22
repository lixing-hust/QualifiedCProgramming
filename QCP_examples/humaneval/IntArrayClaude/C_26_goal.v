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
Require Import coins_26.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function contains -----*)

Definition contains_safety_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (n_pre = (Zlength (l))) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.seg a_pre 0 n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition contains_safety_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth (i - 0 ) l 0) = x_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition contains_safety_wit_3 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth (i - 0 ) l 0) <> x_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition contains_safety_wit_4 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg a_pre 0 n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition contains_entail_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre < INT_MAX) |] 
  &&  [| (n_pre = (Zlength (l))) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
|--
  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
.

Definition contains_entail_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth (i - 0 ) l 0) <> x_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
|--
  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
.

Definition contains_return_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (i >= n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
|--
  ([| (0 <> 0) |] 
  &&  [| (list_contains x_pre l ) |] 
  &&  [| (n_pre = (Zlength (l))) |]
  &&  (IntArray.seg a_pre 0 n_pre l ))
  ||
  ([| (0 = 0) |] 
  &&  [| (list_not_contains x_pre l ) |] 
  &&  [| (n_pre = (Zlength (l))) |]
  &&  (IntArray.seg a_pre 0 n_pre l ))
.

Definition contains_return_wit_2 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) ,
  [| ((Znth (i - 0 ) l 0) = x_pre) |] 
  &&  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
|--
  ([| (1 <> 0) |] 
  &&  [| (list_contains x_pre l ) |] 
  &&  [| (n_pre = (Zlength (l))) |]
  &&  (IntArray.seg a_pre 0 n_pre l ))
  ||
  ([| (1 = 0) |] 
  &&  [| (list_not_contains x_pre l ) |] 
  &&  [| (n_pre = (Zlength (l))) |]
  &&  (IntArray.seg a_pre 0 n_pre l ))
.

Definition contains_partial_solve_wit_1 := 
forall (x_pre: Z) (n_pre: Z) (a_pre: Z) (l: (@list Z)) (i: Z) ,
  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (IntArray.seg a_pre 0 n_pre l )
|--
  [| (i < n_pre) |] 
  &&  [| (n_pre = (Zlength (l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= n_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (l) (0)) <> x_pre)) |]
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i - 0 ) l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

(*----- Function remove_duplicates -----*)

Definition remove_duplicates_safety_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_duplicates_safety_wit_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((( &( "has1_size" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 numbers_size_pre )
  **  ((( &( "has1" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_duplicates_safety_wit_3 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((( &( "has2_size" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_4 numbers_size_pre )
  **  ((( &( "has2" ) )) # Ptr  |-> retval_4)
  **  ((( &( "has1_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 numbers_size_pre )
  **  ((( &( "has1" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_duplicates_safety_wit_4 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "has2_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_4 numbers_size_pre )
  **  ((( &( "has2" ) )) # Ptr  |-> retval_4)
  **  ((( &( "has1_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 numbers_size_pre )
  **  ((( &( "has1" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_duplicates_safety_wit_5 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| False |]
.

Definition remove_duplicates_safety_wit_6 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| False |]
.

Definition remove_duplicates_safety_wit_7 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  ((( &( "in_has1" ) )) # Int  |-> retval_2)
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| False |]
.

Definition remove_duplicates_safety_wit_8 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  ((( &( "in_has1" ) )) # Int  |-> retval_2)
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| False |]
.

Definition remove_duplicates_safety_wit_9 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((has2 + (has2_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg has2 (has2_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  ((( &( "in_has1" ) )) # Int  |-> retval_2)
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
|--
  [| ((has2_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (has2_size + 1 )) |]
.

Definition remove_duplicates_safety_wit_10 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((has2 + (has2_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg has2 (has2_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  ((( &( "in_has1" ) )) # Int  |-> retval_2)
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition remove_duplicates_safety_wit_11 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (((has1 + (has1_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg has1 (has1_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  ((( &( "in_has1" ) )) # Int  |-> retval_2)
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| ((has1_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (has1_size + 1 )) |]
.

Definition remove_duplicates_safety_wit_12 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (((has1 + (has1_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg has1 (has1_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  ((( &( "in_has1" ) )) # Int  |-> retval_2)
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition remove_duplicates_safety_wit_13 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_duplicates_safety_wit_14 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (((has1 + (has1_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg has1 (has1_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> (has1_size + 1 ))
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_duplicates_safety_wit_15 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((has2 + (has2_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg has2 (has2_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> (has2_size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_duplicates_safety_wit_16 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |]
  &&  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_duplicates_safety_wit_17 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |]
  &&  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition remove_duplicates_safety_wit_18 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2_second" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current2" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| False |]
.

Definition remove_duplicates_safety_wit_19 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2_second" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current2" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| False |]
.

Definition remove_duplicates_safety_wit_20 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (output_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2_second" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current2" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition remove_duplicates_safety_wit_21 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (output_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2_second" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current2" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition remove_duplicates_safety_wit_22 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_duplicates_safety_wit_23 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (output_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition remove_duplicates_entail_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) ,
  [| (retval_4 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  (IntArray.undef_full retval_4 numbers_size_pre )
  **  (IntArray.undef_full retval_3 numbers_size_pre )
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  EX (has2_l: (@list Z))  (has1_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_4 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (Zlength (has1_l))) |] 
  &&  [| (0 = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l 0 has1_l has2_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  (IntArray.seg retval_3 0 0 has1_l )
  **  (IntArray.undef_seg retval_3 0 numbers_size_pre )
  **  (IntArray.seg retval_4 0 0 has2_l )
  **  (IntArray.undef_seg retval_4 0 numbers_size_pre )
.

Definition remove_duplicates_entail_wit_2_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_2_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_3_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_3_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_4_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_4_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_5_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_5_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_6_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l_2: (@list Z)) (has1_l_2: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l_2 ) |] 
  &&  [| (has1_size = (Zlength (has1_l_2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l_2 ) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l_2))) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l_2 has2_l_2 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((has2 + (has2_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg has2 (has2_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l_2 )
  **  (IntArray.seg has2 0 has2_size has2_l_2 )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
|--
  EX (has2_l: (@list Z))  (has1_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= (i + 1 )) |] 
  &&  [| (0 <= (has2_size + 1 )) |] 
  &&  [| ((has2_size + 1 ) <= (i + 1 )) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| ((has2_size + 1 ) = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l (i + 1 ) has1_l has2_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 (has2_size + 1 ) has2_l )
  **  (IntArray.undef_seg has2 (has2_size + 1 ) numbers_size_pre )
.

Definition remove_duplicates_entail_wit_6_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l_2: (@list Z)) (has1_l_2: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l_2 ) |] 
  &&  [| (has1_size = (Zlength (has1_l_2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l_2 ) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l_2))) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l_2 has2_l_2 ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (((has1 + (has1_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg has1 (has1_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l_2 )
  **  (IntArray.seg has2 0 has2_size has2_l_2 )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  EX (has2_l: (@list Z))  (has1_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size_pre) |] 
  &&  [| (0 <= (has1_size + 1 )) |] 
  &&  [| ((has1_size + 1 ) <= (i + 1 )) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= (i + 1 )) |] 
  &&  [| ((has1_size + 1 ) = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l (i + 1 ) has1_l has2_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 (has1_size + 1 ) has1_l )
  **  (IntArray.undef_seg has1 (has1_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_6_3 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l_2: (@list Z)) (has1_l_2: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l_2 ) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l_2))) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l_2 has2_l_2 ) |] 
  &&  [| (retval <> 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l_2 )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l_2 )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  EX (has2_l: (@list Z))  (has1_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= (i + 1 )) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= (i + 1 )) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l (i + 1 ) has1_l has2_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_7 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l_2: (@list Z)) (has1_l_2: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l_2))) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l_2 has2_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l_2 )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l_2 )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  EX (output_l: (@list Z))  (has2_l: (@list Z))  (has1_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (0 = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l 0 output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 0 output_l )
  **  (IntArray.undef_seg data 0 numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_8_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (has2_l_2: (@list Z)) (has1_l_2: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l_2 ) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l_2))) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l_2 has2_l_2 ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l_2 i output_l_2 ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.undef_seg data (output_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l_2 )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.seg has1 0 has1_size has1_l_2 )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  EX (output_l: (@list Z))  (has2_l: (@list Z))  (has1_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) <= (i + 1 )) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_entail_wit_8_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (has2_l_2: (@list Z)) (has1_l_2: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has2_l_2 ) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l_2))) |] 
  &&  [| (has2_size = (Zlength (has2_l_2))) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l_2 has2_l_2 ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l_2 i output_l_2 ) |]
  &&  (IntArray.seg has2 0 has2_size has2_l_2 )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l_2 )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  EX (output_l: (@list Z))  (has2_l: (@list Z))  (has1_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_return_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l_2: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size_2: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data_2: Z) (out: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l_2 ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data_2 0 output_size_2 output_l_2 )
  **  (IntArray.undef_seg data_2 output_size_2 numbers_size_pre )
|--
  EX (data: Z)  (output_l: (@list Z))  (output_size: Z) ,
  [| (out <> 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (problem_26_spec input_l output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre input_l )
.

Definition remove_duplicates_partial_solve_wit_2_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (numbers_size_pre >= 0) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
.

Definition remove_duplicates_partial_solve_wit_2_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (numbers_size_pre >= 0) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
.

Definition remove_duplicates_partial_solve_wit_2 := remove_duplicates_partial_solve_wit_2_pure -> remove_duplicates_partial_solve_wit_2_aux.

Definition remove_duplicates_partial_solve_wit_3_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((( &( "has1" ) )) # Ptr  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (numbers_size_pre >= 0) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
.

Definition remove_duplicates_partial_solve_wit_3_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (numbers_size_pre >= 0) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
.

Definition remove_duplicates_partial_solve_wit_3 := remove_duplicates_partial_solve_wit_3_pure -> remove_duplicates_partial_solve_wit_3_aux.

Definition remove_duplicates_partial_solve_wit_4_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  ((( &( "has2" ) )) # Ptr  |->_)
  **  ((( &( "has1_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 numbers_size_pre )
  **  ((( &( "has1" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (numbers_size_pre >= 0) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
.

Definition remove_duplicates_partial_solve_wit_4_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  (IntArray.undef_full retval_3 numbers_size_pre )
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
|--
  [| (numbers_size_pre >= 0) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (retval_3 <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (problem_26_pre input_l ) |]
  &&  (IntArray.undef_full retval_3 numbers_size_pre )
  **  (IntArray.undef_full retval_2 numbers_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
.

Definition remove_duplicates_partial_solve_wit_4 := remove_duplicates_partial_solve_wit_4_pure -> remove_duplicates_partial_solve_wit_4_aux.

Definition remove_duplicates_partial_solve_wit_5 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |]
  &&  (((numbers_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i numbers_pre i 0 numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_6_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |]
  &&  ((( &( "in_has2" ) )) # Int  |->_)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (0 <= has2_size) |] 
  &&  [| (has2_size < INT_MAX) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |]
.

Definition remove_duplicates_partial_solve_wit_6_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (0 <= has2_size) |] 
  &&  [| (has2_size < INT_MAX) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_6 := remove_duplicates_partial_solve_wit_6_pure -> remove_duplicates_partial_solve_wit_6_aux.

Definition remove_duplicates_partial_solve_wit_7_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |]
  &&  ((( &( "in_has1" ) )) # Int  |->_)
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  ((( &( "in_has2" ) )) # Int  |-> retval)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (0 <= has1_size) |] 
  &&  [| (has1_size < INT_MAX) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |]
.

Definition remove_duplicates_partial_solve_wit_7_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (0 <= has1_size) |] 
  &&  [| (has1_size < INT_MAX) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_7 := remove_duplicates_partial_solve_wit_7_pure -> remove_duplicates_partial_solve_wit_7_aux.

Definition remove_duplicates_partial_solve_wit_8 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((has2 + (has2_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg has2 (has2_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_9 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has1_l ) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= i) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l i has1_l has2_l ) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval_2 = 0) |]
  &&  (((has1 + (has1_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg has1 (has1_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_full data numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_10 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (((numbers_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i numbers_pre i 0 numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_11_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  ((( &( "in_has2_second" ) )) # Int  |->_)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((( &( "current2" ) )) # Int  |-> (Znth i input_l 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (0 <= has2_size) |] 
  &&  [| (has2_size < INT_MAX) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |]
.

Definition remove_duplicates_partial_solve_wit_11_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (0 <= has2_size) |] 
  &&  [| (has2_size < INT_MAX) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_11 := remove_duplicates_partial_solve_wit_11_pure -> remove_duplicates_partial_solve_wit_11_aux.

Definition remove_duplicates_partial_solve_wit_12 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l 0) has2_l ) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_13_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (has1 <> 0) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
.

Definition remove_duplicates_partial_solve_wit_13_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (has1 <> 0) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (IntArray.seg has1 0 has1_size has1_l )
  **  (IntArray.undef_seg has1 has1_size numbers_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_13 := remove_duplicates_partial_solve_wit_13_pure -> remove_duplicates_partial_solve_wit_13_aux.

Definition remove_duplicates_partial_solve_wit_14_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "has1" ) )) # Ptr  |-> has1)
  **  ((( &( "has2" ) )) # Ptr  |-> has2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "has1_size" ) )) # Int  |-> has1_size)
  **  ((( &( "has2_size" ) )) # Int  |-> has2_size)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (has2 <> 0) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
.

Definition remove_duplicates_partial_solve_wit_14_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (input_l: (@list Z)) (output_l: (@list Z)) (has2_l: (@list Z)) (has1_l: (@list Z)) (output_size: Z) (has2_size: Z) (has1_size: Z) (i: Z) (has2: Z) (has1: Z) (data: Z) (out: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
  **  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
|--
  [| (has2 <> 0) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (i >= numbers_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (has1 <> 0) |] 
  &&  [| (has2 <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |] 
  &&  [| (numbers_size_pre = (Zlength (input_l))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (0 <= has1_size) |] 
  &&  [| (has1_size <= numbers_size_pre) |] 
  &&  [| (0 <= has2_size) |] 
  &&  [| (has2_size <= numbers_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (has1_size = (Zlength (has1_l))) |] 
  &&  [| (has2_size = (Zlength (has2_l))) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (remove_duplicates_first_loop input_l numbers_size_pre has1_l has2_l ) |] 
  &&  [| (remove_duplicates_second_loop input_l has2_l i output_l ) |]
  &&  (IntArray.seg has2 0 has2_size has2_l )
  **  (IntArray.undef_seg has2 has2_size numbers_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full numbers_pre numbers_size_pre input_l )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size numbers_size_pre )
.

Definition remove_duplicates_partial_solve_wit_14 := remove_duplicates_partial_solve_wit_14_pure -> remove_duplicates_partial_solve_wit_14_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_contains_safety_wit_1 : contains_safety_wit_1.
Axiom proof_of_contains_safety_wit_2 : contains_safety_wit_2.
Axiom proof_of_contains_safety_wit_3 : contains_safety_wit_3.
Axiom proof_of_contains_safety_wit_4 : contains_safety_wit_4.
Axiom proof_of_contains_entail_wit_1 : contains_entail_wit_1.
Axiom proof_of_contains_entail_wit_2 : contains_entail_wit_2.
Axiom proof_of_contains_return_wit_1 : contains_return_wit_1.
Axiom proof_of_contains_return_wit_2 : contains_return_wit_2.
Axiom proof_of_contains_partial_solve_wit_1 : contains_partial_solve_wit_1.
Axiom proof_of_remove_duplicates_safety_wit_1 : remove_duplicates_safety_wit_1.
Axiom proof_of_remove_duplicates_safety_wit_2 : remove_duplicates_safety_wit_2.
Axiom proof_of_remove_duplicates_safety_wit_3 : remove_duplicates_safety_wit_3.
Axiom proof_of_remove_duplicates_safety_wit_4 : remove_duplicates_safety_wit_4.
Axiom proof_of_remove_duplicates_safety_wit_5 : remove_duplicates_safety_wit_5.
Axiom proof_of_remove_duplicates_safety_wit_6 : remove_duplicates_safety_wit_6.
Axiom proof_of_remove_duplicates_safety_wit_7 : remove_duplicates_safety_wit_7.
Axiom proof_of_remove_duplicates_safety_wit_8 : remove_duplicates_safety_wit_8.
Axiom proof_of_remove_duplicates_safety_wit_9 : remove_duplicates_safety_wit_9.
Axiom proof_of_remove_duplicates_safety_wit_10 : remove_duplicates_safety_wit_10.
Axiom proof_of_remove_duplicates_safety_wit_11 : remove_duplicates_safety_wit_11.
Axiom proof_of_remove_duplicates_safety_wit_12 : remove_duplicates_safety_wit_12.
Axiom proof_of_remove_duplicates_safety_wit_13 : remove_duplicates_safety_wit_13.
Axiom proof_of_remove_duplicates_safety_wit_14 : remove_duplicates_safety_wit_14.
Axiom proof_of_remove_duplicates_safety_wit_15 : remove_duplicates_safety_wit_15.
Axiom proof_of_remove_duplicates_safety_wit_16 : remove_duplicates_safety_wit_16.
Axiom proof_of_remove_duplicates_safety_wit_17 : remove_duplicates_safety_wit_17.
Axiom proof_of_remove_duplicates_safety_wit_18 : remove_duplicates_safety_wit_18.
Axiom proof_of_remove_duplicates_safety_wit_19 : remove_duplicates_safety_wit_19.
Axiom proof_of_remove_duplicates_safety_wit_20 : remove_duplicates_safety_wit_20.
Axiom proof_of_remove_duplicates_safety_wit_21 : remove_duplicates_safety_wit_21.
Axiom proof_of_remove_duplicates_safety_wit_22 : remove_duplicates_safety_wit_22.
Axiom proof_of_remove_duplicates_safety_wit_23 : remove_duplicates_safety_wit_23.
Axiom proof_of_remove_duplicates_entail_wit_1 : remove_duplicates_entail_wit_1.
Axiom proof_of_remove_duplicates_entail_wit_2_1 : remove_duplicates_entail_wit_2_1.
Axiom proof_of_remove_duplicates_entail_wit_2_2 : remove_duplicates_entail_wit_2_2.
Axiom proof_of_remove_duplicates_entail_wit_3_1 : remove_duplicates_entail_wit_3_1.
Axiom proof_of_remove_duplicates_entail_wit_3_2 : remove_duplicates_entail_wit_3_2.
Axiom proof_of_remove_duplicates_entail_wit_4_1 : remove_duplicates_entail_wit_4_1.
Axiom proof_of_remove_duplicates_entail_wit_4_2 : remove_duplicates_entail_wit_4_2.
Axiom proof_of_remove_duplicates_entail_wit_5_1 : remove_duplicates_entail_wit_5_1.
Axiom proof_of_remove_duplicates_entail_wit_5_2 : remove_duplicates_entail_wit_5_2.
Axiom proof_of_remove_duplicates_entail_wit_6_1 : remove_duplicates_entail_wit_6_1.
Axiom proof_of_remove_duplicates_entail_wit_6_2 : remove_duplicates_entail_wit_6_2.
Axiom proof_of_remove_duplicates_entail_wit_6_3 : remove_duplicates_entail_wit_6_3.
Axiom proof_of_remove_duplicates_entail_wit_7 : remove_duplicates_entail_wit_7.
Axiom proof_of_remove_duplicates_entail_wit_8_1 : remove_duplicates_entail_wit_8_1.
Axiom proof_of_remove_duplicates_entail_wit_8_2 : remove_duplicates_entail_wit_8_2.
Axiom proof_of_remove_duplicates_return_wit_1 : remove_duplicates_return_wit_1.
Axiom proof_of_remove_duplicates_partial_solve_wit_1 : remove_duplicates_partial_solve_wit_1.
Axiom proof_of_remove_duplicates_partial_solve_wit_2_pure : remove_duplicates_partial_solve_wit_2_pure.
Axiom proof_of_remove_duplicates_partial_solve_wit_2 : remove_duplicates_partial_solve_wit_2.
Axiom proof_of_remove_duplicates_partial_solve_wit_3_pure : remove_duplicates_partial_solve_wit_3_pure.
Axiom proof_of_remove_duplicates_partial_solve_wit_3 : remove_duplicates_partial_solve_wit_3.
Axiom proof_of_remove_duplicates_partial_solve_wit_4_pure : remove_duplicates_partial_solve_wit_4_pure.
Axiom proof_of_remove_duplicates_partial_solve_wit_4 : remove_duplicates_partial_solve_wit_4.
Axiom proof_of_remove_duplicates_partial_solve_wit_5 : remove_duplicates_partial_solve_wit_5.
Axiom proof_of_remove_duplicates_partial_solve_wit_6_pure : remove_duplicates_partial_solve_wit_6_pure.
Axiom proof_of_remove_duplicates_partial_solve_wit_6 : remove_duplicates_partial_solve_wit_6.
Axiom proof_of_remove_duplicates_partial_solve_wit_7_pure : remove_duplicates_partial_solve_wit_7_pure.
Axiom proof_of_remove_duplicates_partial_solve_wit_7 : remove_duplicates_partial_solve_wit_7.
Axiom proof_of_remove_duplicates_partial_solve_wit_8 : remove_duplicates_partial_solve_wit_8.
Axiom proof_of_remove_duplicates_partial_solve_wit_9 : remove_duplicates_partial_solve_wit_9.
Axiom proof_of_remove_duplicates_partial_solve_wit_10 : remove_duplicates_partial_solve_wit_10.
Axiom proof_of_remove_duplicates_partial_solve_wit_11_pure : remove_duplicates_partial_solve_wit_11_pure.
Axiom proof_of_remove_duplicates_partial_solve_wit_11 : remove_duplicates_partial_solve_wit_11.
Axiom proof_of_remove_duplicates_partial_solve_wit_12 : remove_duplicates_partial_solve_wit_12.
Axiom proof_of_remove_duplicates_partial_solve_wit_13_pure : remove_duplicates_partial_solve_wit_13_pure.
Axiom proof_of_remove_duplicates_partial_solve_wit_13 : remove_duplicates_partial_solve_wit_13.
Axiom proof_of_remove_duplicates_partial_solve_wit_14_pure : remove_duplicates_partial_solve_wit_14_pure.
Axiom proof_of_remove_duplicates_partial_solve_wit_14 : remove_duplicates_partial_solve_wit_14.

End VC_Correct.
