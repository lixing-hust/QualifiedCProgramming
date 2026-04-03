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

(*----- Function intersperse -----*)

Definition intersperse_safety_wit_1 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersperse_safety_wit_2 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersperse_safety_wit_3 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition intersperse_safety_wit_4 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg out_pre 1 (2 * numbers_size_pre ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  [| ((0 + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (0 + 1 )) |]
.

Definition intersperse_safety_wit_5 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg out_pre 1 (2 * numbers_size_pre ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersperse_safety_wit_6 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg out_pre 1 (2 * numbers_size_pre ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "k" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersperse_safety_wit_7 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  (IntArray.undef_seg out (k + 1 ) (2 * numbers_size ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers)
  **  (IntArray.full numbers numbers_size l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (IntArray.seg out 0 k out_l )
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter)
|--
  [| ((k + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (k + 1 )) |]
.

Definition intersperse_safety_wit_8 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  (IntArray.undef_seg out (k + 1 ) (2 * numbers_size ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers)
  **  (IntArray.full numbers numbers_size l )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (IntArray.seg out 0 k out_l )
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersperse_safety_wit_9 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + ((k + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.undef_seg out ((k + 1 ) + 1 ) (2 * numbers_size ) )
  **  (IntArray.full numbers numbers_size l )
  **  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (IntArray.seg out 0 k out_l )
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter)
|--
  [| (((k + 1 ) + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((k + 1 ) + 1 )) |]
.

Definition intersperse_safety_wit_10 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + ((k + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.undef_seg out ((k + 1 ) + 1 ) (2 * numbers_size ) )
  **  (IntArray.full numbers numbers_size l )
  **  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (IntArray.seg out 0 k out_l )
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition intersperse_safety_wit_11 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + ((k + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.undef_seg out ((k + 1 ) + 1 ) (2 * numbers_size ) )
  **  (IntArray.full numbers numbers_size l )
  **  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size)
  **  ((( &( "k" ) )) # Int  |-> ((k + 1 ) + 1 ))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (IntArray.seg out 0 k out_l )
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition intersperse_entail_wit_1 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg out_pre 1 (2 * numbers_size_pre ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= 1) |] 
  &&  [| (1 <= numbers_size_pre) |] 
  &&  [| ((0 + 1 ) = ((2 * 1 ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (1 - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter_pre) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 (0 + 1 ) out_l )
  **  (IntArray.undef_seg out_pre (0 + 1 ) (2 * numbers_size_pre ) )
.

Definition intersperse_entail_wit_2 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l_2: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l_2 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l_2 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l_2 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + ((k + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.undef_seg out ((k + 1 ) + 1 ) (2 * numbers_size ) )
  **  (IntArray.full numbers numbers_size l )
  **  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  (IntArray.seg out 0 k out_l_2 )
|--
  EX (out_l: (@list Z)) ,
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size) |] 
  &&  [| (((k + 1 ) + 1 ) = ((2 * (i + 1 ) ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < ((i + 1 ) - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (IntArray.full numbers numbers_size l )
  **  (IntArray.seg out 0 ((k + 1 ) + 1 ) out_l )
  **  (IntArray.undef_seg out ((k + 1 ) + 1 ) (2 * numbers_size ) )
.

Definition intersperse_return_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (numbers_size_pre = 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
|--
  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
.

Definition intersperse_return_wit_2 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i >= numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (IntArray.full numbers numbers_size l )
  **  (IntArray.seg out 0 k out_l )
  **  (IntArray.undef_seg out k (2 * numbers_size ) )
|--
  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
.

Definition intersperse_partial_solve_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
|--
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((numbers_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i numbers_pre 0 0 numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
.

Definition intersperse_partial_solve_wit_2 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre (2 * numbers_size_pre ) )
|--
  [| (numbers_size_pre <> 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre 1 (2 * numbers_size_pre ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
.

Definition intersperse_partial_solve_wit_3 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (IntArray.full numbers numbers_size l )
  **  (IntArray.seg out 0 k out_l )
  **  (IntArray.undef_seg out k (2 * numbers_size ) )
|--
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out (k + 1 ) (2 * numbers_size ) )
  **  (IntArray.full numbers numbers_size l )
  **  (IntArray.seg out 0 k out_l )
.

Definition intersperse_partial_solve_wit_4 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  (IntArray.undef_seg out (k + 1 ) (2 * numbers_size ) )
  **  (IntArray.full numbers numbers_size l )
  **  (IntArray.seg out 0 k out_l )
|--
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((numbers + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i numbers i 0 numbers_size l )
  **  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  (IntArray.undef_seg out (k + 1 ) (2 * numbers_size ) )
  **  (IntArray.seg out 0 k out_l )
.

Definition intersperse_partial_solve_wit_5 := 
forall (l: (@list Z)) (delimeter: Z) (out: Z) (out_l: (@list Z)) (numbers: Z) (k: Z) (numbers_size: Z) (i: Z) ,
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (IntArray.full numbers numbers_size l )
  **  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  (IntArray.undef_seg out (k + 1 ) (2 * numbers_size ) )
  **  (IntArray.seg out 0 k out_l )
|--
  [| (i < numbers_size) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= numbers_size) |] 
  &&  [| (k = ((2 * i ) - 1 )) |] 
  &&  [| ((Znth 0 out_l 0) = (Znth 0 l 0)) |] 
  &&  [| forall (j: Z) , (((0 <= j) /\ (j < (i - 1 ))) -> (((Znth ((2 * j ) + 1 ) out_l 0) = delimeter) /\ ((Znth (2 * (j + 1 ) ) out_l 0) = (Znth (j + 1 ) l 0)))) |]
  &&  (((out + ((k + 1 ) * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out ((k + 1 ) + 1 ) (2 * numbers_size ) )
  **  (IntArray.full numbers numbers_size l )
  **  (((out + (k * sizeof(INT) ) )) # Int  |-> delimeter)
  **  (IntArray.seg out 0 k out_l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_intersperse_safety_wit_1 : intersperse_safety_wit_1.
Axiom proof_of_intersperse_safety_wit_2 : intersperse_safety_wit_2.
Axiom proof_of_intersperse_safety_wit_3 : intersperse_safety_wit_3.
Axiom proof_of_intersperse_safety_wit_4 : intersperse_safety_wit_4.
Axiom proof_of_intersperse_safety_wit_5 : intersperse_safety_wit_5.
Axiom proof_of_intersperse_safety_wit_6 : intersperse_safety_wit_6.
Axiom proof_of_intersperse_safety_wit_7 : intersperse_safety_wit_7.
Axiom proof_of_intersperse_safety_wit_8 : intersperse_safety_wit_8.
Axiom proof_of_intersperse_safety_wit_9 : intersperse_safety_wit_9.
Axiom proof_of_intersperse_safety_wit_10 : intersperse_safety_wit_10.
Axiom proof_of_intersperse_safety_wit_11 : intersperse_safety_wit_11.
Axiom proof_of_intersperse_entail_wit_1 : intersperse_entail_wit_1.
Axiom proof_of_intersperse_entail_wit_2 : intersperse_entail_wit_2.
Axiom proof_of_intersperse_return_wit_1 : intersperse_return_wit_1.
Axiom proof_of_intersperse_return_wit_2 : intersperse_return_wit_2.
Axiom proof_of_intersperse_partial_solve_wit_1 : intersperse_partial_solve_wit_1.
Axiom proof_of_intersperse_partial_solve_wit_2 : intersperse_partial_solve_wit_2.
Axiom proof_of_intersperse_partial_solve_wit_3 : intersperse_partial_solve_wit_3.
Axiom proof_of_intersperse_partial_solve_wit_4 : intersperse_partial_solve_wit_4.
Axiom proof_of_intersperse_partial_solve_wit_5 : intersperse_partial_solve_wit_5.

End VC_Correct.
