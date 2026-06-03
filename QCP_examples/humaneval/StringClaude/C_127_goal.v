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
Require Import coins_127.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function intersection -----*)

Definition intersection_safety_wit_1 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  ((( &( "s1" ) )) # Int  |->_)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersection_safety_wit_2 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  ((( &( "e1" ) )) # Int  |->_)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  ((( &( "s1" ) )) # Int  |-> (Znth 0 i1 0))
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersection_safety_wit_3 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  ((( &( "s2" ) )) # Int  |->_)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  ((( &( "e1" ) )) # Int  |-> (Znth 1 i1 0))
  **  ((( &( "s1" ) )) # Int  |-> (Znth 0 i1 0))
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersection_safety_wit_4 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  ((( &( "e2" ) )) # Int  |->_)
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  ((( &( "s2" ) )) # Int  |-> (Znth 0 i2 0))
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  ((( &( "e1" ) )) # Int  |-> (Znth 1 i1 0))
  **  ((( &( "s1" ) )) # Int  |-> (Znth 0 i1 0))
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersection_safety_wit_5 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| ((Znth 1 i1 0) >= (Znth 1 i2 0)) |] 
  &&  [| ((Znth 0 i1 0) <= (Znth 0 i2 0)) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  ((( &( "l" ) )) # Int  |->_)
  **  ((( &( "inter2" ) )) # Int  |-> (Znth 1 i2 0))
  **  ((( &( "inter1" ) )) # Int  |-> (Znth 0 i2 0))
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  ((( &( "e2" ) )) # Int  |-> (Znth 1 i2 0))
  **  ((( &( "s2" ) )) # Int  |-> (Znth 0 i2 0))
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  ((( &( "e1" ) )) # Int  |-> (Znth 1 i1 0))
  **  ((( &( "s1" ) )) # Int  |-> (Znth 0 i1 0))
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
|--
  [| (((Znth 1 i2 0) - (Znth 0 i2 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 1 i2 0) - (Znth 0 i2 0) )) |]
.

Definition intersection_safety_wit_6 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| ((Znth 1 i1 0) >= (Znth 1 i2 0)) |] 
  &&  [| ((Znth 0 i1 0) > (Znth 0 i2 0)) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  ((( &( "l" ) )) # Int  |->_)
  **  ((( &( "inter2" ) )) # Int  |-> (Znth 1 i2 0))
  **  ((( &( "inter1" ) )) # Int  |-> (Znth 0 i1 0))
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  ((( &( "e2" ) )) # Int  |-> (Znth 1 i2 0))
  **  ((( &( "s2" ) )) # Int  |-> (Znth 0 i2 0))
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  ((( &( "e1" ) )) # Int  |-> (Znth 1 i1 0))
  **  ((( &( "s1" ) )) # Int  |-> (Znth 0 i1 0))
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
|--
  [| (((Znth 1 i2 0) - (Znth 0 i1 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 1 i2 0) - (Znth 0 i1 0) )) |]
.

Definition intersection_safety_wit_7 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| ((Znth 1 i1 0) < (Znth 1 i2 0)) |] 
  &&  [| ((Znth 0 i1 0) <= (Znth 0 i2 0)) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  ((( &( "l" ) )) # Int  |->_)
  **  ((( &( "inter2" ) )) # Int  |-> (Znth 1 i1 0))
  **  ((( &( "inter1" ) )) # Int  |-> (Znth 0 i2 0))
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  ((( &( "e2" ) )) # Int  |-> (Znth 1 i2 0))
  **  ((( &( "s2" ) )) # Int  |-> (Znth 0 i2 0))
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  ((( &( "e1" ) )) # Int  |-> (Znth 1 i1 0))
  **  ((( &( "s1" ) )) # Int  |-> (Znth 0 i1 0))
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
|--
  [| (((Znth 1 i1 0) - (Znth 0 i2 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 1 i1 0) - (Znth 0 i2 0) )) |]
.

Definition intersection_safety_wit_8 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| ((Znth 1 i1 0) < (Znth 1 i2 0)) |] 
  &&  [| ((Znth 0 i1 0) > (Znth 0 i2 0)) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  ((( &( "l" ) )) # Int  |->_)
  **  ((( &( "inter2" ) )) # Int  |-> (Znth 1 i1 0))
  **  ((( &( "inter1" ) )) # Int  |-> (Znth 0 i1 0))
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  ((( &( "e2" ) )) # Int  |-> (Znth 1 i2 0))
  **  ((( &( "s2" ) )) # Int  |-> (Znth 0 i2 0))
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  ((( &( "e1" ) )) # Int  |-> (Znth 1 i1 0))
  **  ((( &( "s1" ) )) # Int  |-> (Znth 0 i1 0))
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
|--
  [| (((Znth 1 i1 0) - (Znth 0 i1 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth 1 i1 0) - (Znth 0 i1 0) )) |]
.

Definition intersection_safety_wit_9 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (s1: Z) (e1: Z) (s2: Z) (e2: Z) (inter1: Z) (inter2: Z) (l: Z) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= l) |] 
  &&  [| (l <= 2000000000) |]
  &&  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition intersection_safety_wit_10 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (s1: Z) (e1: Z) (s2: Z) (e2: Z) (inter1: Z) (inter2: Z) (l: Z) ,
  [| (l < 2) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= l) |] 
  &&  [| (l <= 2000000000) |]
  &&  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersection_safety_wit_11 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (s1: Z) (e1: Z) (s2: Z) (e2: Z) (inter1: Z) (inter2: Z) (l: Z) ,
  [| (l >= 2) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= l) |] 
  &&  [| (l <= 2000000000) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition intersection_safety_wit_12 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| ((i * i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i * i )) |]
.

Definition intersection_safety_wit_13 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| ((i * i ) <= l) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| ((l <> (INT_MIN)) \/ (i <> (-1))) |] 
  &&  [| (i <> 0) |]
.

Definition intersection_safety_wit_14 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| ((i * i ) <= l) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersection_safety_wit_15 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| ((l % ( i ) ) = 0) |] 
  &&  [| ((i * i ) <= l) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersection_safety_wit_16 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| ((l % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= l) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition intersection_safety_wit_17 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| ((i * i ) > l) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  ((( &( "interval1" ) )) # Ptr  |-> interval1_pre)
  **  ((( &( "interval2" ) )) # Ptr  |-> interval2_pre)
  **  ((( &( "interval1_size" ) )) # Int  |-> interval1_size_pre)
  **  ((( &( "interval2_size" ) )) # Int  |-> interval2_size_pre)
  **  ((( &( "s1" ) )) # Int  |-> s1)
  **  ((( &( "e1" ) )) # Int  |-> e1)
  **  ((( &( "s2" ) )) # Int  |-> s2)
  **  ((( &( "e2" ) )) # Int  |-> e2)
  **  ((( &( "inter1" ) )) # Int  |-> inter1)
  **  ((( &( "inter2" ) )) # Int  |-> inter2)
  **  ((( &( "l" ) )) # Int  |-> l)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersection_entail_wit_1_1 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| ((Znth 1 i1 0) >= (Znth 1 i2 0)) |] 
  &&  [| ((Znth 0 i1 0) <= (Znth 0 i2 0)) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| ((Znth 0 i1 0) = (Znth (0) (i1) (0))) |] 
  &&  [| ((Znth 1 i1 0) = (Znth (1) (i1) (0))) |] 
  &&  [| ((Znth 0 i2 0) = (Znth (0) (i2) (0))) |] 
  &&  [| ((Znth 1 i2 0) = (Znth (1) (i2) (0))) |] 
  &&  [| ((Znth 0 i2 0) = (inter_start_z (i1) (i2))) |] 
  &&  [| ((Znth 1 i2 0) = (inter_end_z (i1) (i2))) |] 
  &&  [| (((Znth 1 i2 0) - (Znth 0 i2 0) ) = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= ((Znth 1 i2 0) - (Znth 0 i2 0) )) |] 
  &&  [| (((Znth 1 i2 0) - (Znth 0 i2 0) ) <= 2000000000) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_entail_wit_1_2 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| ((Znth 1 i1 0) >= (Znth 1 i2 0)) |] 
  &&  [| ((Znth 0 i1 0) > (Znth 0 i2 0)) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| ((Znth 0 i1 0) = (Znth (0) (i1) (0))) |] 
  &&  [| ((Znth 1 i1 0) = (Znth (1) (i1) (0))) |] 
  &&  [| ((Znth 0 i2 0) = (Znth (0) (i2) (0))) |] 
  &&  [| ((Znth 1 i2 0) = (Znth (1) (i2) (0))) |] 
  &&  [| ((Znth 0 i1 0) = (inter_start_z (i1) (i2))) |] 
  &&  [| ((Znth 1 i2 0) = (inter_end_z (i1) (i2))) |] 
  &&  [| (((Znth 1 i2 0) - (Znth 0 i1 0) ) = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= ((Znth 1 i2 0) - (Znth 0 i1 0) )) |] 
  &&  [| (((Znth 1 i2 0) - (Znth 0 i1 0) ) <= 2000000000) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_entail_wit_1_3 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| ((Znth 1 i1 0) < (Znth 1 i2 0)) |] 
  &&  [| ((Znth 0 i1 0) <= (Znth 0 i2 0)) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| ((Znth 0 i1 0) = (Znth (0) (i1) (0))) |] 
  &&  [| ((Znth 1 i1 0) = (Znth (1) (i1) (0))) |] 
  &&  [| ((Znth 0 i2 0) = (Znth (0) (i2) (0))) |] 
  &&  [| ((Znth 1 i2 0) = (Znth (1) (i2) (0))) |] 
  &&  [| ((Znth 0 i2 0) = (inter_start_z (i1) (i2))) |] 
  &&  [| ((Znth 1 i1 0) = (inter_end_z (i1) (i2))) |] 
  &&  [| (((Znth 1 i1 0) - (Znth 0 i2 0) ) = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= ((Znth 1 i1 0) - (Znth 0 i2 0) )) |] 
  &&  [| (((Znth 1 i1 0) - (Znth 0 i2 0) ) <= 2000000000) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_entail_wit_1_4 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| ((Znth 1 i1 0) < (Znth 1 i2 0)) |] 
  &&  [| ((Znth 0 i1 0) > (Znth 0 i2 0)) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| ((Znth 0 i1 0) = (Znth (0) (i1) (0))) |] 
  &&  [| ((Znth 1 i1 0) = (Znth (1) (i1) (0))) |] 
  &&  [| ((Znth 0 i2 0) = (Znth (0) (i2) (0))) |] 
  &&  [| ((Znth 1 i2 0) = (Znth (1) (i2) (0))) |] 
  &&  [| ((Znth 0 i1 0) = (inter_start_z (i1) (i2))) |] 
  &&  [| ((Znth 1 i1 0) = (inter_end_z (i1) (i2))) |] 
  &&  [| (((Znth 1 i1 0) - (Znth 0 i1 0) ) = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= ((Znth 1 i1 0) - (Znth 0 i1 0) )) |] 
  &&  [| (((Znth 1 i1 0) - (Znth 0 i1 0) ) <= 2000000000) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_entail_wit_2 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (s1: Z) (e1: Z) (s2: Z) (e2: Z) (inter1: Z) (inter2: Z) (l: Z) ,
  [| (l >= 2) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= l) |] 
  &&  [| (l <= 2000000000) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= 2) |] 
  &&  [| (2 <= 46340) |] 
  &&  [| (prime_prefix_z 2 l ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_entail_wit_3 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| ((l % ( i ) ) <> 0) |] 
  &&  [| ((i * i ) <= l) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= 46340) |] 
  &&  [| (prime_prefix_z (i + 1 ) l ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_return_wit_1 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| ((i * i ) > l) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (problem_127_spec_z i1 i2 1 ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_return_wit_2 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (i: Z) (l: Z) (inter2: Z) (inter1: Z) (e2: Z) (s2: Z) (e1: Z) (s1: Z) ,
  [| ((l % ( i ) ) = 0) |] 
  &&  [| ((i * i ) <= l) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| (2 <= l) |] 
  &&  [| (l <= 2000000000) |] 
  &&  [| (2 <= i) |] 
  &&  [| (i <= 46340) |] 
  &&  [| (prime_prefix_z i l ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (problem_127_spec_z i1 i2 0 ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_return_wit_3 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) (s1: Z) (e1: Z) (s2: Z) (e2: Z) (inter1: Z) (inter2: Z) (l: Z) ,
  [| (l < 2) |] 
  &&  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |] 
  &&  [| (s1 = (Znth (0) (i1) (0))) |] 
  &&  [| (e1 = (Znth (1) (i1) (0))) |] 
  &&  [| (s2 = (Znth (0) (i2) (0))) |] 
  &&  [| (e2 = (Znth (1) (i2) (0))) |] 
  &&  [| (inter1 = (inter_start_z (i1) (i2))) |] 
  &&  [| (inter2 = (inter_end_z (i1) (i2))) |] 
  &&  [| (l = (inter_len_z (i1) (i2))) |] 
  &&  [| ((-2000000000) <= l) |] 
  &&  [| (l <= 2000000000) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (problem_127_spec_z i1 i2 0 ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_partial_solve_wit_1 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (((interval1_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 i1 0))
  **  (IntArray.missing_i interval1_pre 0 0 interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_partial_solve_wit_2 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (((interval1_pre + (1 * sizeof(INT) ) )) # Int  |-> (Znth 1 i1 0))
  **  (IntArray.missing_i interval1_pre 1 0 interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
.

Definition intersection_partial_solve_wit_3 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (IntArray.full interval1_pre interval1_size_pre i1 )
  **  (IntArray.full interval2_pre interval2_size_pre i2 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (((interval2_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 i2 0))
  **  (IntArray.missing_i interval2_pre 0 0 interval2_size_pre i2 )
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
.

Definition intersection_partial_solve_wit_4 := 
forall (interval2_size_pre: Z) (interval2_pre: Z) (interval1_size_pre: Z) (interval1_pre: Z) (i2: (@list Z)) (i1: (@list Z)) ,
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (IntArray.full interval2_pre interval2_size_pre i2 )
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
|--
  [| (interval1_size_pre = 2) |] 
  &&  [| (interval2_size_pre = 2) |] 
  &&  [| (problem_127_pre_z i1 i2 ) |] 
  &&  [| (interval_int_range i1 ) |] 
  &&  [| (interval_int_range i2 ) |]
  &&  (((interval2_pre + (1 * sizeof(INT) ) )) # Int  |-> (Znth 1 i2 0))
  **  (IntArray.missing_i interval2_pre 1 0 interval2_size_pre i2 )
  **  (IntArray.full interval1_pre interval1_size_pre i1 )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_intersection_safety_wit_1 : intersection_safety_wit_1.
Axiom proof_of_intersection_safety_wit_2 : intersection_safety_wit_2.
Axiom proof_of_intersection_safety_wit_3 : intersection_safety_wit_3.
Axiom proof_of_intersection_safety_wit_4 : intersection_safety_wit_4.
Axiom proof_of_intersection_safety_wit_5 : intersection_safety_wit_5.
Axiom proof_of_intersection_safety_wit_6 : intersection_safety_wit_6.
Axiom proof_of_intersection_safety_wit_7 : intersection_safety_wit_7.
Axiom proof_of_intersection_safety_wit_8 : intersection_safety_wit_8.
Axiom proof_of_intersection_safety_wit_9 : intersection_safety_wit_9.
Axiom proof_of_intersection_safety_wit_10 : intersection_safety_wit_10.
Axiom proof_of_intersection_safety_wit_11 : intersection_safety_wit_11.
Axiom proof_of_intersection_safety_wit_12 : intersection_safety_wit_12.
Axiom proof_of_intersection_safety_wit_13 : intersection_safety_wit_13.
Axiom proof_of_intersection_safety_wit_14 : intersection_safety_wit_14.
Axiom proof_of_intersection_safety_wit_15 : intersection_safety_wit_15.
Axiom proof_of_intersection_safety_wit_16 : intersection_safety_wit_16.
Axiom proof_of_intersection_safety_wit_17 : intersection_safety_wit_17.
Axiom proof_of_intersection_entail_wit_1_1 : intersection_entail_wit_1_1.
Axiom proof_of_intersection_entail_wit_1_2 : intersection_entail_wit_1_2.
Axiom proof_of_intersection_entail_wit_1_3 : intersection_entail_wit_1_3.
Axiom proof_of_intersection_entail_wit_1_4 : intersection_entail_wit_1_4.
Axiom proof_of_intersection_entail_wit_2 : intersection_entail_wit_2.
Axiom proof_of_intersection_entail_wit_3 : intersection_entail_wit_3.
Axiom proof_of_intersection_return_wit_1 : intersection_return_wit_1.
Axiom proof_of_intersection_return_wit_2 : intersection_return_wit_2.
Axiom proof_of_intersection_return_wit_3 : intersection_return_wit_3.
Axiom proof_of_intersection_partial_solve_wit_1 : intersection_partial_solve_wit_1.
Axiom proof_of_intersection_partial_solve_wit_2 : intersection_partial_solve_wit_2.
Axiom proof_of_intersection_partial_solve_wit_3 : intersection_partial_solve_wit_3.
Axiom proof_of_intersection_partial_solve_wit_4 : intersection_partial_solve_wit_4.

End VC_Correct.
