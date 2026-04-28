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
Require Import coins_58.
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

(*----- Function common -----*)

Definition common_safety_wit_1 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition common_safety_wit_2 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l1_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition common_safety_wit_3 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l1_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition common_safety_wit_4 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "in_output" ) )) # Int  |-> retval)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l1 0))
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| False |]
.

Definition common_safety_wit_5 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "in_output" ) )) # Int  |-> retval)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l1 0))
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| False |]
.

Definition common_safety_wit_6 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  ((( &( "in_l2" ) )) # Int  |-> retval_2)
  **  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "in_output" ) )) # Int  |-> retval)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l1 0))
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| False |]
.

Definition common_safety_wit_7 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  ((( &( "in_l2" ) )) # Int  |-> retval_2)
  **  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "in_output" ) )) # Int  |-> retval)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l1 0))
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| False |]
.

Definition common_safety_wit_8 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l1 0))
  **  (IntArray.undef_seg data (output_size + 1 ) l1_size_pre )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  ((( &( "in_l2" ) )) # Int  |-> retval_2)
  **  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "in_output" ) )) # Int  |-> retval)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l1 0))
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| ((output_size + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (output_size + 1 )) |]
.

Definition common_safety_wit_9 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l1 0))
  **  (IntArray.undef_seg data (output_size + 1 ) l1_size_pre )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  ((( &( "in_l2" ) )) # Int  |-> retval_2)
  **  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "in_output" ) )) # Int  |-> retval)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l1 0))
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition common_safety_wit_10 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition common_safety_wit_11 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition common_safety_wit_12 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l1 0))
  **  (IntArray.undef_seg data (output_size + 1 ) l1_size_pre )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition common_safety_wit_13 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition common_entail_wit_1 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  (IntArray.undef_full retval_2 l1_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
|--
  EX (output_l: (@list Z)) ,
  [| (retval <> 0) |] 
  &&  [| (retval_2 <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 0 output_l ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg retval_2 0 0 output_l )
  **  (IntArray.undef_seg retval_2 0 l1_size_pre )
.

Definition common_entail_wit_2_1 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_entail_wit_2_2 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_entail_wit_3_1 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_entail_wit_3_2 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_entail_wit_4_1 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l_2 ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |-> (Znth i input_l1 0))
  **  (IntArray.undef_seg data (output_size + 1 ) l1_size_pre )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l1_size_pre) |] 
  &&  [| (0 <= (output_size + 1 )) |] 
  &&  [| ((output_size + 1 ) <= (i + 1 )) |] 
  &&  [| ((output_size + 1 ) = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 (output_size + 1 ) output_l )
  **  (IntArray.undef_seg data (output_size + 1 ) l1_size_pre )
.

Definition common_entail_wit_4_2 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l_2 ) |] 
  &&  [| (retval_2 = 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_entail_wit_4_3 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) output_l_2 ) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l_2))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l_2 ) |]
  &&  (IntArray.seg data 0 output_size output_l_2 )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  EX (output_l: (@list Z)) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= (i + 1 )) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 (i + 1 ) output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_return_wit_1 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l_2: (@list Z)) (output_size_2: Z) (i: Z) (data_2: Z) (out: Z) (sorted_full_l: (@list Z)) (sorted_l: (@list Z)) ,
  [| (output_size_2 = (Zlength (sorted_l))) |] 
  &&  [| (l1_size_pre = (Zlength (sorted_full_l))) |] 
  &&  [| ((sublist (0) (output_size_2) (sorted_full_l)) = sorted_l) |] 
  &&  [| (sorted_int_list_by 1 sorted_l ) |] 
  &&  [| (Permutation output_l_2 sorted_l ) |] 
  &&  [| (i >= l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data_2 <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size_2) |] 
  &&  [| (output_size_2 <= i) |] 
  &&  [| (output_size_2 = (Zlength (output_l_2))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l_2 ) |]
  &&  (IntArray.full data_2 l1_size_pre sorted_full_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
|--
  EX (data_l: (@list Z))  (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= l1_size_pre) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (l1_size_pre = (Zlength (data_l))) |] 
  &&  [| ((sublist (0) (output_size) (data_l)) = output_l) |] 
  &&  [| (problem_58_spec_z input_l1 input_l2 output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
  **  (IntArray.full data l1_size_pre data_l )
.

Definition common_partial_solve_wit_1 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) ,
  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
|--
  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
.

Definition common_partial_solve_wit_2_pure := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
|--
  [| (l1_size_pre >= 0) |] 
  &&  [| (l1_size_pre < INT_MAX) |]
.

Definition common_partial_solve_wit_2_aux := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (retval: Z) ,
  [| (retval <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
|--
  [| (l1_size_pre >= 0) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (retval <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |]
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.full l2_pre l2_size_pre input_l2 )
.

Definition common_partial_solve_wit_2 := common_partial_solve_wit_2_pure -> common_partial_solve_wit_2_aux.

Definition common_partial_solve_wit_3 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (((l1_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l1 0))
  **  (IntArray.missing_i l1_pre i 0 l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_partial_solve_wit_4_pure := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  ((( &( "in_output" ) )) # Int  |->_)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l1 0))
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (0 <= output_size) |] 
  &&  [| (output_size < INT_MAX) |] 
  &&  [| (output_size = (Zlength (output_l))) |]
.

Definition common_partial_solve_wit_4_aux := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (0 <= output_size) |] 
  &&  [| (output_size < INT_MAX) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_partial_solve_wit_4 := common_partial_solve_wit_4_pure -> common_partial_solve_wit_4_aux.

Definition common_partial_solve_wit_5_pure := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  ((( &( "in_l2" ) )) # Int  |->_)
  **  (IntArray.seg data 0 output_size output_l )
  **  ((( &( "in_output" ) )) # Int  |-> retval)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((( &( "current" ) )) # Int  |-> (Znth i input_l1 0))
  **  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |]
.

Definition common_partial_solve_wit_5_aux := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) ,
  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
.

Definition common_partial_solve_wit_5 := common_partial_solve_wit_5_pure -> common_partial_solve_wit_5_aux.

Definition common_partial_solve_wit_6 := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (retval_2 <> 0) |] 
  &&  [| (list_contains (Znth i input_l1 0) input_l2 ) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (retval = 0) |] 
  &&  [| (retval = 0) |] 
  &&  [| (list_not_contains (Znth i input_l1 0) output_l ) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (i < l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |] 
  &&  [| (retval_2 <> 0) |]
  &&  (((data + (output_size * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) l1_size_pre )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
.

Definition common_partial_solve_wit_7_pure := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  ((( &( "l1" ) )) # Ptr  |-> l1_pre)
  **  ((( &( "l1_size" ) )) # Int  |-> l1_size_pre)
  **  ((( &( "l2" ) )) # Ptr  |-> l2_pre)
  **  ((( &( "l2_size" ) )) # Int  |-> l2_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (data <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= l1_size_pre) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |]
.

Definition common_partial_solve_wit_7_aux := 
forall (l2_size_pre: Z) (l2_pre: Z) (l1_size_pre: Z) (l1_pre: Z) (input_l2: (@list Z)) (input_l1: (@list Z)) (output_l: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) ,
  [| (i >= l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
  **  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
|--
  [| (data <> 0) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= l1_size_pre) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (i >= l1_size_pre) |] 
  &&  [| (out <> 0) |] 
  &&  [| (data <> 0) |] 
  &&  [| (0 <= l1_size_pre) |] 
  &&  [| (l1_size_pre < INT_MAX) |] 
  &&  [| (0 <= l2_size_pre) |] 
  &&  [| (l2_size_pre < INT_MAX) |] 
  &&  [| (l1_size_pre = (Zlength (input_l1))) |] 
  &&  [| (l2_size_pre = (Zlength (input_l2))) |] 
  &&  [| (problem_58_pre_z input_l1 input_l2 ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l1_size_pre) |] 
  &&  [| (0 <= output_size) |] 
  &&  [| (output_size <= i) |] 
  &&  [| (output_size = (Zlength (output_l))) |] 
  &&  [| (common_first_loop input_l1 input_l2 i output_l ) |]
  &&  (IntArray.seg data 0 output_size output_l )
  **  (IntArray.undef_seg data output_size l1_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l1_pre l1_size_pre input_l1 )
  **  (IntArray.seg l2_pre 0 l2_size_pre input_l2 )
.

Definition common_partial_solve_wit_7 := common_partial_solve_wit_7_pure -> common_partial_solve_wit_7_aux.

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
Axiom proof_of_common_safety_wit_1 : common_safety_wit_1.
Axiom proof_of_common_safety_wit_2 : common_safety_wit_2.
Axiom proof_of_common_safety_wit_3 : common_safety_wit_3.
Axiom proof_of_common_safety_wit_4 : common_safety_wit_4.
Axiom proof_of_common_safety_wit_5 : common_safety_wit_5.
Axiom proof_of_common_safety_wit_6 : common_safety_wit_6.
Axiom proof_of_common_safety_wit_7 : common_safety_wit_7.
Axiom proof_of_common_safety_wit_8 : common_safety_wit_8.
Axiom proof_of_common_safety_wit_9 : common_safety_wit_9.
Axiom proof_of_common_safety_wit_10 : common_safety_wit_10.
Axiom proof_of_common_safety_wit_11 : common_safety_wit_11.
Axiom proof_of_common_safety_wit_12 : common_safety_wit_12.
Axiom proof_of_common_safety_wit_13 : common_safety_wit_13.
Axiom proof_of_common_entail_wit_1 : common_entail_wit_1.
Axiom proof_of_common_entail_wit_2_1 : common_entail_wit_2_1.
Axiom proof_of_common_entail_wit_2_2 : common_entail_wit_2_2.
Axiom proof_of_common_entail_wit_3_1 : common_entail_wit_3_1.
Axiom proof_of_common_entail_wit_3_2 : common_entail_wit_3_2.
Axiom proof_of_common_entail_wit_4_1 : common_entail_wit_4_1.
Axiom proof_of_common_entail_wit_4_2 : common_entail_wit_4_2.
Axiom proof_of_common_entail_wit_4_3 : common_entail_wit_4_3.
Axiom proof_of_common_return_wit_1 : common_return_wit_1.
Axiom proof_of_common_partial_solve_wit_1 : common_partial_solve_wit_1.
Axiom proof_of_common_partial_solve_wit_2_pure : common_partial_solve_wit_2_pure.
Axiom proof_of_common_partial_solve_wit_2 : common_partial_solve_wit_2.
Axiom proof_of_common_partial_solve_wit_3 : common_partial_solve_wit_3.
Axiom proof_of_common_partial_solve_wit_4_pure : common_partial_solve_wit_4_pure.
Axiom proof_of_common_partial_solve_wit_4 : common_partial_solve_wit_4.
Axiom proof_of_common_partial_solve_wit_5_pure : common_partial_solve_wit_5_pure.
Axiom proof_of_common_partial_solve_wit_5 : common_partial_solve_wit_5.
Axiom proof_of_common_partial_solve_wit_6 : common_partial_solve_wit_6.
Axiom proof_of_common_partial_solve_wit_7_pure : common_partial_solve_wit_7_pure.
Axiom proof_of_common_partial_solve_wit_7 : common_partial_solve_wit_7.

End VC_Correct.
