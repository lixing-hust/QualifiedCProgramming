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

(*----- Function move_one_ball -----*)

Definition move_one_ball_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition move_one_ball_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition move_one_ball_safety_wit_3 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((i - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i - 1 )) |]
.

Definition move_one_ball_safety_wit_4 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition move_one_ball_safety_wit_5 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth i lv 0) < (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((num + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num + 1 )) |]
.

Definition move_one_ball_safety_wit_6 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth i lv 0) < (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition move_one_ball_safety_wit_7 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth i lv 0) < (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> (num + 1 ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition move_one_ball_safety_wit_8 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition move_one_ball_safety_wit_9 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((arr_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (arr_size_pre - 1 )) |]
.

Definition move_one_ball_safety_wit_10 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition move_one_ball_safety_wit_11 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition move_one_ball_safety_wit_12 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth (arr_size_pre - 1 ) lv 0) > (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| ((num + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num + 1 )) |]
.

Definition move_one_ball_safety_wit_13 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth (arr_size_pre - 1 ) lv 0) > (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition move_one_ball_safety_wit_14 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth (arr_size_pre - 1 ) lv 0) > (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> (num + 1 ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition move_one_ball_safety_wit_15 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth (arr_size_pre - 1 ) lv 0) <= (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition move_one_ball_safety_wit_16 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((num + 1 ) < 2) |] 
  &&  [| ((Znth (arr_size_pre - 1 ) lv 0) > (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> (num + 1 ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition move_one_ball_safety_wit_17 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (num < 2) |] 
  &&  [| ((Znth (arr_size_pre - 1 ) lv 0) <= (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition move_one_ball_safety_wit_18 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((num + 1 ) >= 2) |] 
  &&  [| ((Znth (arr_size_pre - 1 ) lv 0) > (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> (num + 1 ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition move_one_ball_safety_wit_19 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (num >= 2) |] 
  &&  [| ((Znth (arr_size_pre - 1 ) lv 0) <= (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition move_one_ball_entail_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  [| (1 <= 1) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (0 = (count_descents_prefix (1) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition move_one_ball_entail_wit_2_1 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth i lv 0) >= (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix ((i + 1 )) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
.

Definition move_one_ball_entail_wit_2_2 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((Znth i lv 0) < (Znth (i - 1 ) lv 0)) |] 
  &&  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= arr_size_pre) |] 
  &&  [| ((num + 1 ) = (count_descents_prefix ((i + 1 )) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
.

Definition move_one_ball_return_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((num + 1 ) < 2) |] 
  &&  [| ((Znth (arr_size_pre - 1 ) lv 0) > (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  ([| (1 = 0) |] 
  &&  [| ((cyclic_descents (lv)) >= 2) |]
  &&  (IntArray.full arr_pre arr_size_pre lv ))
  ||
  ([| (1 <> 0) |] 
  &&  [| ((cyclic_descents (lv)) < 2) |]
  &&  (IntArray.full arr_pre arr_size_pre lv ))
.

Definition move_one_ball_return_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (num < 2) |] 
  &&  [| ((Znth (arr_size_pre - 1 ) lv 0) <= (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  ([| (1 = 0) |] 
  &&  [| ((cyclic_descents (lv)) >= 2) |]
  &&  (IntArray.full arr_pre arr_size_pre lv ))
  ||
  ([| (1 <> 0) |] 
  &&  [| ((cyclic_descents (lv)) < 2) |]
  &&  (IntArray.full arr_pre arr_size_pre lv ))
.

Definition move_one_ball_return_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| ((num + 1 ) >= 2) |] 
  &&  [| ((Znth (arr_size_pre - 1 ) lv 0) > (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  ([| (0 = 0) |] 
  &&  [| ((cyclic_descents (lv)) >= 2) |]
  &&  (IntArray.full arr_pre arr_size_pre lv ))
  ||
  ([| (0 <> 0) |] 
  &&  [| ((cyclic_descents (lv)) < 2) |]
  &&  (IntArray.full arr_pre arr_size_pre lv ))
.

Definition move_one_ball_return_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (num >= 2) |] 
  &&  [| ((Znth (arr_size_pre - 1 ) lv 0) <= (Znth 0 lv 0)) |] 
  &&  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  ([| (0 = 0) |] 
  &&  [| ((cyclic_descents (lv)) >= 2) |]
  &&  (IntArray.full arr_pre arr_size_pre lv ))
  ||
  ([| (0 <> 0) |] 
  &&  [| ((cyclic_descents (lv)) < 2) |]
  &&  (IntArray.full arr_pre arr_size_pre lv ))
.

Definition move_one_ball_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (((arr + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i arr i 0 arr_size_pre lv )
.

Definition move_one_ball_partial_solve_wit_2 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (i < arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (((arr + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (i - 1 ) lv 0))
  **  (IntArray.missing_i arr (i - 1 ) 0 arr_size_pre lv )
.

Definition move_one_ball_partial_solve_wit_3 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (((arr + ((arr_size_pre - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth (arr_size_pre - 1 ) lv 0))
  **  (IntArray.missing_i arr (arr_size_pre - 1 ) 0 arr_size_pre lv )
.

Definition move_one_ball_partial_solve_wit_4 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (num: Z) (i: Z) ,
  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (IntArray.full arr arr_size_pre lv )
|--
  [| (i >= arr_size_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= arr_size_pre) |] 
  &&  [| (num = (count_descents_prefix (i) (lv))) |] 
  &&  [| (1 <= arr_size_pre) |] 
  &&  [| (arr_size_pre < INT_MAX) |]
  &&  (((arr + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 lv 0))
  **  (IntArray.missing_i arr 0 0 arr_size_pre lv )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_move_one_ball_safety_wit_1 : move_one_ball_safety_wit_1.
Axiom proof_of_move_one_ball_safety_wit_2 : move_one_ball_safety_wit_2.
Axiom proof_of_move_one_ball_safety_wit_3 : move_one_ball_safety_wit_3.
Axiom proof_of_move_one_ball_safety_wit_4 : move_one_ball_safety_wit_4.
Axiom proof_of_move_one_ball_safety_wit_5 : move_one_ball_safety_wit_5.
Axiom proof_of_move_one_ball_safety_wit_6 : move_one_ball_safety_wit_6.
Axiom proof_of_move_one_ball_safety_wit_7 : move_one_ball_safety_wit_7.
Axiom proof_of_move_one_ball_safety_wit_8 : move_one_ball_safety_wit_8.
Axiom proof_of_move_one_ball_safety_wit_9 : move_one_ball_safety_wit_9.
Axiom proof_of_move_one_ball_safety_wit_10 : move_one_ball_safety_wit_10.
Axiom proof_of_move_one_ball_safety_wit_11 : move_one_ball_safety_wit_11.
Axiom proof_of_move_one_ball_safety_wit_12 : move_one_ball_safety_wit_12.
Axiom proof_of_move_one_ball_safety_wit_13 : move_one_ball_safety_wit_13.
Axiom proof_of_move_one_ball_safety_wit_14 : move_one_ball_safety_wit_14.
Axiom proof_of_move_one_ball_safety_wit_15 : move_one_ball_safety_wit_15.
Axiom proof_of_move_one_ball_safety_wit_16 : move_one_ball_safety_wit_16.
Axiom proof_of_move_one_ball_safety_wit_17 : move_one_ball_safety_wit_17.
Axiom proof_of_move_one_ball_safety_wit_18 : move_one_ball_safety_wit_18.
Axiom proof_of_move_one_ball_safety_wit_19 : move_one_ball_safety_wit_19.
Axiom proof_of_move_one_ball_entail_wit_1 : move_one_ball_entail_wit_1.
Axiom proof_of_move_one_ball_entail_wit_2_1 : move_one_ball_entail_wit_2_1.
Axiom proof_of_move_one_ball_entail_wit_2_2 : move_one_ball_entail_wit_2_2.
Axiom proof_of_move_one_ball_return_wit_1 : move_one_ball_return_wit_1.
Axiom proof_of_move_one_ball_return_wit_2 : move_one_ball_return_wit_2.
Axiom proof_of_move_one_ball_return_wit_3 : move_one_ball_return_wit_3.
Axiom proof_of_move_one_ball_return_wit_4 : move_one_ball_return_wit_4.
Axiom proof_of_move_one_ball_partial_solve_wit_1 : move_one_ball_partial_solve_wit_1.
Axiom proof_of_move_one_ball_partial_solve_wit_2 : move_one_ball_partial_solve_wit_2.
Axiom proof_of_move_one_ball_partial_solve_wit_3 : move_one_ball_partial_solve_wit_3.
Axiom proof_of_move_one_ball_partial_solve_wit_4 : move_one_ball_partial_solve_wit_4.

End VC_Correct.
