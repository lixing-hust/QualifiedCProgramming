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

(*----- Function two_sum_sorted -----*)

Definition two_sum_sorted_safety_wit_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition two_sum_sorted_safety_wit_2 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| ((n_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre - 1 )) |]
.

Definition two_sum_sorted_safety_wit_3 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition two_sum_sorted_safety_wit_4 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < left)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ (right < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "s" ) )) # Int  |->_)
|--
  [| (((Znth left l 0) + (Znth right l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((Znth left l 0) + (Znth right l 0) )) |]
.

Definition two_sum_sorted_safety_wit_5 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (s: Z) (left: Z) (right: Z) ,
  [| (s = target_pre) |] 
  &&  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , (((((0 <= i_3) /\ (i_3 < j_3)) /\ (j_3 < n_pre)) /\ (i_3 < left)) -> (((Znth i_3 l 0) + (Znth j_3 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , (((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) /\ (right < j_4)) -> (((Znth i_4 l 0) + (Znth j_4 l 0) ) <> target_pre)) |]
  &&  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition two_sum_sorted_safety_wit_6 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (s: Z) (left: Z) (right: Z) ,
  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (((Znth left l 0) + (Znth right l 0) ) < target_pre) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , (((((0 <= i_3) /\ (i_3 < j_3)) /\ (j_3 < n_pre)) /\ (i_3 < left)) -> (((Znth i_3 l 0) + (Znth j_3 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , (((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) /\ (right < j_4)) -> (((Znth i_4 l 0) + (Znth j_4 l 0) ) <> target_pre)) |]
  &&  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| ((left + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (left + 1 )) |]
.

Definition two_sum_sorted_safety_wit_7 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (s: Z) (left: Z) (right: Z) ,
  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (target_pre < ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , (((((0 <= i_3) /\ (i_3 < j_3)) /\ (j_3 < n_pre)) /\ (i_3 < left)) -> (((Znth i_3 l 0) + (Znth j_3 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , (((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) /\ (right < j_4)) -> (((Znth i_4 l 0) + (Znth j_4 l 0) ) <> target_pre)) |]
  &&  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  [| ((right - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (right - 1 )) |]
.

Definition two_sum_sorted_safety_wit_8 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left >= right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < left)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ (right < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full a_pre n_pre l )
  **  ((( &( "s" ) )) # Int  |->_)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition two_sum_sorted_entail_wit_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| ((-1) <= (n_pre - 1 )) |] 
  &&  [| ((n_pre - 1 ) < n_pre) |] 
  &&  [| (0 <= ((n_pre - 1 ) + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < 0)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ ((n_pre - 1 ) < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition two_sum_sorted_entail_wit_2 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_7: Z) , forall (j_7: Z) , ((((0 <= i_7) /\ (i_7 <= j_7)) /\ (j_7 < n_pre)) -> ((Znth i_7 l 0) <= (Znth j_7 l 0))) |] 
  &&  [| forall (i_8: Z) , forall (j_8: Z) , ((((0 <= i_8) /\ (i_8 < j_8)) /\ (j_8 < n_pre)) -> ((INT_MIN <= ((Znth i_8 l 0) + (Znth j_8 l 0) )) /\ (((Znth i_8 l 0) + (Znth j_8 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_9: Z) , forall (j_9: Z) , (((((0 <= i_9) /\ (i_9 < j_9)) /\ (j_9 < n_pre)) /\ (i_9 < left)) -> (((Znth i_9 l 0) + (Znth j_9 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_10: Z) , forall (j_10: Z) , (((((0 <= i_10) /\ (i_10 < j_10)) /\ (j_10 < n_pre)) /\ (right < j_10)) -> (((Znth i_10 l 0) + (Znth j_10 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , ((((0 <= i_5) /\ (i_5 <= j_5)) /\ (j_5 < n_pre)) -> ((Znth i_5 l 0) <= (Znth j_5 l 0))) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , ((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) -> ((INT_MIN <= ((Znth i_6 l 0) + (Znth j_6 l 0) )) /\ (((Znth i_6 l 0) + (Znth j_6 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (((Znth left l 0) + (Znth right l 0) ) = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , (((((0 <= i_3) /\ (i_3 < j_3)) /\ (j_3 < n_pre)) /\ (i_3 < left)) -> (((Znth i_3 l 0) + (Znth j_3 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , (((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) /\ (right < j_4)) -> (((Znth i_4 l 0) + (Znth j_4 l 0) ) <> target_pre)) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition two_sum_sorted_entail_wit_3 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (s: Z) (left: Z) (right: Z) ,
  [| (s < target_pre) |] 
  &&  [| (s <> target_pre) |] 
  &&  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , ((((0 <= i_5) /\ (i_5 <= j_5)) /\ (j_5 < n_pre)) -> ((Znth i_5 l 0) <= (Znth j_5 l 0))) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , ((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) -> ((INT_MIN <= ((Znth i_6 l 0) + (Znth j_6 l 0) )) /\ (((Znth i_6 l 0) + (Znth j_6 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_7: Z) , forall (j_7: Z) , (((((0 <= i_7) /\ (i_7 < j_7)) /\ (j_7 < n_pre)) /\ (i_7 < left)) -> (((Znth i_7 l 0) + (Znth j_7 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_8: Z) , forall (j_8: Z) , (((((0 <= i_8) /\ (i_8 < j_8)) /\ (j_8 < n_pre)) /\ (right < j_8)) -> (((Znth i_8 l 0) + (Znth j_8 l 0) ) <> target_pre)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (((Znth left l 0) + (Znth right l 0) ) < target_pre) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , (((((0 <= i_3) /\ (i_3 < j_3)) /\ (j_3 < n_pre)) /\ (i_3 < left)) -> (((Znth i_3 l 0) + (Znth j_3 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , (((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) /\ (right < j_4)) -> (((Znth i_4 l 0) + (Znth j_4 l 0) ) <> target_pre)) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition two_sum_sorted_entail_wit_4 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (s: Z) (left: Z) (right: Z) ,
  [| (s >= target_pre) |] 
  &&  [| (s <> target_pre) |] 
  &&  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , ((((0 <= i_5) /\ (i_5 <= j_5)) /\ (j_5 < n_pre)) -> ((Znth i_5 l 0) <= (Znth j_5 l 0))) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , ((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) -> ((INT_MIN <= ((Znth i_6 l 0) + (Znth j_6 l 0) )) /\ (((Znth i_6 l 0) + (Znth j_6 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_7: Z) , forall (j_7: Z) , (((((0 <= i_7) /\ (i_7 < j_7)) /\ (j_7 < n_pre)) /\ (i_7 < left)) -> (((Znth i_7 l 0) + (Znth j_7 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_8: Z) , forall (j_8: Z) , (((((0 <= i_8) /\ (i_8 < j_8)) /\ (j_8 < n_pre)) /\ (right < j_8)) -> (((Znth i_8 l 0) + (Znth j_8 l 0) ) <> target_pre)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (target_pre < ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , (((((0 <= i_3) /\ (i_3 < j_3)) /\ (j_3 < n_pre)) /\ (i_3 < left)) -> (((Znth i_3 l 0) + (Znth j_3 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , (((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) /\ (right < j_4)) -> (((Znth i_4 l 0) + (Znth j_4 l 0) ) <> target_pre)) |]
  &&  (IntArray.full a_pre n_pre l )
.

Definition two_sum_sorted_entail_wit_5_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (s: Z) (left: Z) (right: Z) ,
  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (target_pre < ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_7: Z) , forall (j_7: Z) , ((((0 <= i_7) /\ (i_7 <= j_7)) /\ (j_7 < n_pre)) -> ((Znth i_7 l 0) <= (Znth j_7 l 0))) |] 
  &&  [| forall (i_8: Z) , forall (j_8: Z) , ((((0 <= i_8) /\ (i_8 < j_8)) /\ (j_8 < n_pre)) -> ((INT_MIN <= ((Znth i_8 l 0) + (Znth j_8 l 0) )) /\ (((Znth i_8 l 0) + (Znth j_8 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_9: Z) , forall (j_9: Z) , (((((0 <= i_9) /\ (i_9 < j_9)) /\ (j_9 < n_pre)) /\ (i_9 < left)) -> (((Znth i_9 l 0) + (Znth j_9 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_10: Z) , forall (j_10: Z) , (((((0 <= i_10) /\ (i_10 < j_10)) /\ (j_10 < n_pre)) /\ (right < j_10)) -> (((Znth i_10 l 0) + (Znth j_10 l 0) ) <> target_pre)) |]
  &&  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= (right - 1 )) |] 
  &&  [| ((right - 1 ) < n_pre) |] 
  &&  [| (left <= ((right - 1 ) + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < left)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ ((right - 1 ) < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "s" ) )) # Int  |->_)
.

Definition two_sum_sorted_entail_wit_5_2 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (s: Z) (left: Z) (right: Z) ,
  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (((Znth left l 0) + (Znth right l 0) ) < target_pre) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_7: Z) , forall (j_7: Z) , ((((0 <= i_7) /\ (i_7 <= j_7)) /\ (j_7 < n_pre)) -> ((Znth i_7 l 0) <= (Znth j_7 l 0))) |] 
  &&  [| forall (i_8: Z) , forall (j_8: Z) , ((((0 <= i_8) /\ (i_8 < j_8)) /\ (j_8 < n_pre)) -> ((INT_MIN <= ((Znth i_8 l 0) + (Znth j_8 l 0) )) /\ (((Znth i_8 l 0) + (Znth j_8 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_9: Z) , forall (j_9: Z) , (((((0 <= i_9) /\ (i_9 < j_9)) /\ (j_9 < n_pre)) /\ (i_9 < left)) -> (((Znth i_9 l 0) + (Znth j_9 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_10: Z) , forall (j_10: Z) , (((((0 <= i_10) /\ (i_10 < j_10)) /\ (j_10 < n_pre)) /\ (right < j_10)) -> (((Znth i_10 l 0) + (Znth j_10 l 0) ) <> target_pre)) |]
  &&  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full a_pre n_pre l )
|--
  [| (0 <= (left + 1 )) |] 
  &&  [| ((left + 1 ) <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| ((left + 1 ) <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < (left + 1 ))) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ (right < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "s" ) )) # Int  |->_)
.

Definition two_sum_sorted_return_wit_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (s: Z) (left: Z) (right: Z) ,
  [| (s = target_pre) |] 
  &&  [| (s = ((Znth left l 0) + (Znth right l 0) )) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left < right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < left)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ (right < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (1 = 0) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> (((Znth i l 0) + (Znth j l 0) ) <> target_pre)) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  (EX (j_2: Z)  (i_2: Z) ,
  [| (1 = 1) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < j_2) |] 
  &&  [| (j_2 < n_pre) |] 
  &&  [| (((Znth i_2 l 0) + (Znth j_2 l 0) ) = target_pre) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition two_sum_sorted_return_wit_2 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left >= right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , ((((0 <= i_5) /\ (i_5 <= j_5)) /\ (j_5 < n_pre)) -> ((Znth i_5 l 0) <= (Znth j_5 l 0))) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , ((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) -> ((INT_MIN <= ((Znth i_6 l 0) + (Znth j_6 l 0) )) /\ (((Znth i_6 l 0) + (Znth j_6 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_7: Z) , forall (j_7: Z) , (((((0 <= i_7) /\ (i_7 < j_7)) /\ (j_7 < n_pre)) /\ (i_7 < left)) -> (((Znth i_7 l 0) + (Znth j_7 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_8: Z) , forall (j_8: Z) , (((((0 <= i_8) /\ (i_8 < j_8)) /\ (j_8 < n_pre)) /\ (right < j_8)) -> (((Znth i_8 l 0) + (Znth j_8 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  ([| (0 = 0) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i < j)) /\ (j < n_pre)) -> (((Znth i l 0) + (Znth j l 0) ) <> target_pre)) |]
  &&  (IntArray.full a_pre n_pre l ))
  ||
  (EX (j_2: Z)  (i_2: Z) ,
  [| (0 = 1) |] 
  &&  [| (0 <= i_2) |] 
  &&  [| (i_2 < j_2) |] 
  &&  [| (j_2 < n_pre) |] 
  &&  [| (((Znth i_2 l 0) + (Znth j_2 l 0) ) = target_pre) |]
  &&  (IntArray.full a_pre n_pre l ))
.

Definition two_sum_sorted_partial_solve_wit_1 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < left)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ (right < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < left)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ (right < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (((a_pre + (left * sizeof(INT) ) )) # Int  |-> (Znth left l 0))
  **  (IntArray.missing_i a_pre left 0 n_pre l )
.

Definition two_sum_sorted_partial_solve_wit_2 := 
forall (target_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (right: Z) (left: Z) ,
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < left)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ (right < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (IntArray.full a_pre n_pre l )
|--
  [| (left < right) |] 
  &&  [| (0 <= left) |] 
  &&  [| (left <= n_pre) |] 
  &&  [| ((-1) <= right) |] 
  &&  [| (right < n_pre) |] 
  &&  [| (left <= (right + 1 )) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i_3: Z) , forall (j_3: Z) , ((((0 <= i_3) /\ (i_3 <= j_3)) /\ (j_3 < n_pre)) -> ((Znth i_3 l 0) <= (Znth j_3 l 0))) |] 
  &&  [| forall (i_4: Z) , forall (j_4: Z) , ((((0 <= i_4) /\ (i_4 < j_4)) /\ (j_4 < n_pre)) -> ((INT_MIN <= ((Znth i_4 l 0) + (Znth j_4 l 0) )) /\ (((Znth i_4 l 0) + (Znth j_4 l 0) ) <= INT_MAX))) |] 
  &&  [| forall (i_5: Z) , forall (j_5: Z) , (((((0 <= i_5) /\ (i_5 < j_5)) /\ (j_5 < n_pre)) /\ (i_5 < left)) -> (((Znth i_5 l 0) + (Znth j_5 l 0) ) <> target_pre)) |] 
  &&  [| forall (i_6: Z) , forall (j_6: Z) , (((((0 <= i_6) /\ (i_6 < j_6)) /\ (j_6 < n_pre)) /\ (right < j_6)) -> (((Znth i_6 l 0) + (Znth j_6 l 0) ) <> target_pre)) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |] 
  &&  [| ((Zlength (l)) = n_pre) |] 
  &&  [| forall (i: Z) , forall (j: Z) , ((((0 <= i) /\ (i <= j)) /\ (j < n_pre)) -> ((Znth i l 0) <= (Znth j l 0))) |] 
  &&  [| forall (i_2: Z) , forall (j_2: Z) , ((((0 <= i_2) /\ (i_2 < j_2)) /\ (j_2 < n_pre)) -> ((INT_MIN <= ((Znth i_2 l 0) + (Znth j_2 l 0) )) /\ (((Znth i_2 l 0) + (Znth j_2 l 0) ) <= INT_MAX))) |]
  &&  (((a_pre + (right * sizeof(INT) ) )) # Int  |-> (Znth right l 0))
  **  (IntArray.missing_i a_pre right 0 n_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_two_sum_sorted_safety_wit_1 : two_sum_sorted_safety_wit_1.
Axiom proof_of_two_sum_sorted_safety_wit_2 : two_sum_sorted_safety_wit_2.
Axiom proof_of_two_sum_sorted_safety_wit_3 : two_sum_sorted_safety_wit_3.
Axiom proof_of_two_sum_sorted_safety_wit_4 : two_sum_sorted_safety_wit_4.
Axiom proof_of_two_sum_sorted_safety_wit_5 : two_sum_sorted_safety_wit_5.
Axiom proof_of_two_sum_sorted_safety_wit_6 : two_sum_sorted_safety_wit_6.
Axiom proof_of_two_sum_sorted_safety_wit_7 : two_sum_sorted_safety_wit_7.
Axiom proof_of_two_sum_sorted_safety_wit_8 : two_sum_sorted_safety_wit_8.
Axiom proof_of_two_sum_sorted_entail_wit_1 : two_sum_sorted_entail_wit_1.
Axiom proof_of_two_sum_sorted_entail_wit_2 : two_sum_sorted_entail_wit_2.
Axiom proof_of_two_sum_sorted_entail_wit_3 : two_sum_sorted_entail_wit_3.
Axiom proof_of_two_sum_sorted_entail_wit_4 : two_sum_sorted_entail_wit_4.
Axiom proof_of_two_sum_sorted_entail_wit_5_1 : two_sum_sorted_entail_wit_5_1.
Axiom proof_of_two_sum_sorted_entail_wit_5_2 : two_sum_sorted_entail_wit_5_2.
Axiom proof_of_two_sum_sorted_return_wit_1 : two_sum_sorted_return_wit_1.
Axiom proof_of_two_sum_sorted_return_wit_2 : two_sum_sorted_return_wit_2.
Axiom proof_of_two_sum_sorted_partial_solve_wit_1 : two_sum_sorted_partial_solve_wit_1.
Axiom proof_of_two_sum_sorted_partial_solve_wit_2 : two_sum_sorted_partial_solve_wit_2.

End VC_Correct.
