Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.get_obj_slot_without_critical_inferred_20261013_lib.
Local Open Scope sac.

(*----- Function Get_Obj_Slot_without_critical -----*)

Definition Get_Obj_Slot_without_critical_safety_wit_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "endPtr" ) )) # UInt  |-> e)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Get_Obj_Slot_without_critical_entail_wit_1 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
|--
  “ (p <> 0) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (0 <= e) ” 
  &&  “ (e <= UINT_MAX) ” 
  &&  “ (17 <= 17) ” 
  &&  “ (17 <= (gos_limit (xs))) ” 
  &&  “ ((gos_limit (xs)) <= 255) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ” 
  &&  “ (gos_safe_observation xs e func_object_pre ) ” 
  &&  “ (gos_no_match xs func_object_pre 17 ) ”
  &&  (gos_preserved h )
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  TT && emp 
|--
  “ (gos_no_match xs func_object_pre 17 ) ” 
  &&  “ (gos_safe_observation xs e func_object_pre ) ” 
  &&  “ ((gos_limit (xs)) <= 255) ” 
  &&  “ (17 <= (gos_limit (xs))) ” 
  &&  “ (e <= UINT_MAX) ” 
  &&  “ (0 <= e) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (0 <= prio_pre) ”
  &&  emp
).

Definition Get_Obj_Slot_without_critical_entail_wit_1_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_no_match xs func_object_pre 17 )
.

Definition Get_Obj_Slot_without_critical_entail_wit_1_split_goal_2 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_safe_observation xs e func_object_pre )
.

Definition Get_Obj_Slot_without_critical_entail_wit_1_split_goal_3 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  ((gos_limit (xs)) <= 255)
.

Definition Get_Obj_Slot_without_critical_entail_wit_1_split_goal_4 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (17 <= (gos_limit (xs)))
.

Definition Get_Obj_Slot_without_critical_entail_wit_1_split_goal_5 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (e <= UINT_MAX)
.

Definition Get_Obj_Slot_without_critical_entail_wit_1_split_goal_6 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (0 <= e)
.

Definition Get_Obj_Slot_without_critical_entail_wit_1_split_goal_7 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (prio_pre < 63)
.

Definition Get_Obj_Slot_without_critical_entail_wit_1_split_goal_8 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p <> 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (0 <= prio_pre)
.

Definition Get_Obj_Slot_without_critical_entail_wit_2 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (j_2: Z) (PreH1 : (i = j_2)) (PreH2 : ((gos_nth (xs) (j)) <> func_object_pre)) (PreH3 : (i = j)) (PreH4 : (i < e)) (PreH5 : (p <> 0)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre < 63)) (PreH8 : (0 <= e)) (PreH9 : (e <= UINT_MAX)) (PreH10 : (17 <= i)) (PreH11 : (i <= (gos_limit (xs)))) (PreH12 : ((gos_limit (xs)) <= 255)) (PreH13 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH14 : (gos_safe_observation xs e func_object_pre )) (PreH15 : (gos_no_match xs func_object_pre i )) ,
  (gos_preserved h )
|--
  “ (p <> 0) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (0 <= e) ” 
  &&  “ (e <= UINT_MAX) ” 
  &&  “ (17 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (gos_limit (xs))) ” 
  &&  “ ((gos_limit (xs)) <= 255) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ” 
  &&  “ (gos_safe_observation xs e func_object_pre ) ” 
  &&  “ (gos_no_match xs func_object_pre (i + 1 ) ) ”
  &&  (gos_preserved h )
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (j_2: Z) (PreH1 : (i = j_2)) (PreH2 : ((gos_nth (xs) (j)) <> func_object_pre)) (PreH3 : (i = j)) (PreH4 : (i < e)) (PreH5 : (p <> 0)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre < 63)) (PreH8 : (0 <= e)) (PreH9 : (e <= UINT_MAX)) (PreH10 : (17 <= i)) (PreH11 : (i <= (gos_limit (xs)))) (PreH12 : ((gos_limit (xs)) <= 255)) (PreH13 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH14 : (gos_safe_observation xs e func_object_pre )) (PreH15 : (gos_no_match xs func_object_pre i )) ,
  TT && emp 
|--
  “ (gos_no_match xs func_object_pre (i + 1 ) ) ” 
  &&  “ ((i + 1 ) <= (gos_limit (xs))) ”
  &&  emp
).

Definition Get_Obj_Slot_without_critical_entail_wit_2_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (j_2: Z) (PreH1 : (i = j_2)) (PreH2 : ((gos_nth (xs) (j)) <> func_object_pre)) (PreH3 : (i = j)) (PreH4 : (i < e)) (PreH5 : (p <> 0)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre < 63)) (PreH8 : (0 <= e)) (PreH9 : (e <= UINT_MAX)) (PreH10 : (17 <= i)) (PreH11 : (i <= (gos_limit (xs)))) (PreH12 : ((gos_limit (xs)) <= 255)) (PreH13 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH14 : (gos_safe_observation xs e func_object_pre )) (PreH15 : (gos_no_match xs func_object_pre i )) ,
  (gos_no_match xs func_object_pre (i + 1 ) )
.

Definition Get_Obj_Slot_without_critical_entail_wit_2_split_goal_2 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (j_2: Z) (PreH1 : (i = j_2)) (PreH2 : ((gos_nth (xs) (j)) <> func_object_pre)) (PreH3 : (i = j)) (PreH4 : (i < e)) (PreH5 : (p <> 0)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre < 63)) (PreH8 : (0 <= e)) (PreH9 : (e <= UINT_MAX)) (PreH10 : (17 <= i)) (PreH11 : (i <= (gos_limit (xs)))) (PreH12 : ((gos_limit (xs)) <= 255)) (PreH13 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH14 : (gos_safe_observation xs e func_object_pre )) (PreH15 : (gos_no_match xs func_object_pre i )) ,
  ((i + 1 ) <= (gos_limit (xs)))
.

Definition Get_Obj_Slot_without_critical_return_wit_1 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (PreH1 : (i >= e)) (PreH2 : (p <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= e)) (PreH6 : (e <= UINT_MAX)) (PreH7 : (17 <= i)) (PreH8 : (i <= (gos_limit (xs)))) (PreH9 : ((gos_limit (xs)) <= 255)) (PreH10 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH11 : (gos_safe_observation xs e func_object_pre )) (PreH12 : (gos_no_match xs func_object_pre i )) ,
  (gos_preserved h )
|--
  “ (gos_result prio_pre p e func_object_pre xs 0 ) ”
  &&  (gos_preserved h )
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (PreH1 : (i >= e)) (PreH2 : (p <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= e)) (PreH6 : (e <= UINT_MAX)) (PreH7 : (17 <= i)) (PreH8 : (i <= (gos_limit (xs)))) (PreH9 : ((gos_limit (xs)) <= 255)) (PreH10 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH11 : (gos_safe_observation xs e func_object_pre )) (PreH12 : (gos_no_match xs func_object_pre i )) ,
  TT && emp 
|--
  “ (gos_result prio_pre p e func_object_pre xs 0 ) ”
  &&  emp
).

Definition Get_Obj_Slot_without_critical_return_wit_1_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (PreH1 : (i >= e)) (PreH2 : (p <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= e)) (PreH6 : (e <= UINT_MAX)) (PreH7 : (17 <= i)) (PreH8 : (i <= (gos_limit (xs)))) (PreH9 : ((gos_limit (xs)) <= 255)) (PreH10 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH11 : (gos_safe_observation xs e func_object_pre )) (PreH12 : (gos_no_match xs func_object_pre i )) ,
  (gos_result prio_pre p e func_object_pre xs 0 )
.

Definition Get_Obj_Slot_without_critical_return_wit_2 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (j_2: Z) (PreH1 : (i = j_2)) (PreH2 : ((gos_nth (xs) (j)) = func_object_pre)) (PreH3 : (i = j)) (PreH4 : (i < e)) (PreH5 : (p <> 0)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre < 63)) (PreH8 : (0 <= e)) (PreH9 : (e <= UINT_MAX)) (PreH10 : (17 <= i)) (PreH11 : (i <= (gos_limit (xs)))) (PreH12 : ((gos_limit (xs)) <= 255)) (PreH13 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH14 : (gos_safe_observation xs e func_object_pre )) (PreH15 : (gos_no_match xs func_object_pre i )) ,
  (gos_preserved h )
|--
  “ (gos_result prio_pre p e func_object_pre xs i ) ”
  &&  (gos_preserved h )
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (j_2: Z) (PreH1 : (i = j_2)) (PreH2 : ((gos_nth (xs) (j)) = func_object_pre)) (PreH3 : (i = j)) (PreH4 : (i < e)) (PreH5 : (p <> 0)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre < 63)) (PreH8 : (0 <= e)) (PreH9 : (e <= UINT_MAX)) (PreH10 : (17 <= i)) (PreH11 : (i <= (gos_limit (xs)))) (PreH12 : ((gos_limit (xs)) <= 255)) (PreH13 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH14 : (gos_safe_observation xs e func_object_pre )) (PreH15 : (gos_no_match xs func_object_pre i )) ,
  TT && emp 
|--
  “ (gos_result prio_pre p e func_object_pre xs i ) ”
  &&  emp
).

Definition Get_Obj_Slot_without_critical_return_wit_2_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (j_2: Z) (PreH1 : (i = j_2)) (PreH2 : ((gos_nth (xs) (j)) = func_object_pre)) (PreH3 : (i = j)) (PreH4 : (i < e)) (PreH5 : (p <> 0)) (PreH6 : (0 <= prio_pre)) (PreH7 : (prio_pre < 63)) (PreH8 : (0 <= e)) (PreH9 : (e <= UINT_MAX)) (PreH10 : (17 <= i)) (PreH11 : (i <= (gos_limit (xs)))) (PreH12 : ((gos_limit (xs)) <= 255)) (PreH13 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH14 : (gos_safe_observation xs e func_object_pre )) (PreH15 : (gos_no_match xs func_object_pre i )) ,
  (gos_result prio_pre p e func_object_pre xs i )
.

Definition Get_Obj_Slot_without_critical_return_wit_3 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p = 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
|--
  “ (gos_result prio_pre p e func_object_pre xs 0 ) ”
  &&  (gos_preserved h )
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p = 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  TT && emp 
|--
  “ (gos_result prio_pre 0 e func_object_pre xs 0 ) ”
  &&  emp
).

Definition Get_Obj_Slot_without_critical_return_wit_3_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (p = 0)) (PreH2 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH3 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_result prio_pre 0 e func_object_pre xs 0 )
.

Definition Get_Obj_Slot_without_critical_return_wit_4 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
|--
  “ (gos_result prio_pre p e func_object_pre xs 42 ) ”
  &&  (gos_preserved h )
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  TT && emp 
|--
  “ (gos_result prio_pre p e func_object_pre xs 42 ) ”
  &&  emp
).

Definition Get_Obj_Slot_without_critical_return_wit_4_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) >= 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_result prio_pre p e func_object_pre xs 42 )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_exact h )
|--
  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ”
  &&  (gos_exact h )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_2_pure := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
|--
  “ (gos_read_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e ) ”
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
|--
  “ (gos_read_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e ) ”
).

Definition Get_Obj_Slot_without_critical_partial_solve_wit_2_pure_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
|--
  “ (gos_read_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e ) ”
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_2_aux := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
|--
  “ (gos_read_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e ) ” 
  &&  “ ((unsigned_last_nbits (prio_pre) (32)) < 63) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ”
  &&  (gos_preserved h )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_2 := Get_Obj_Slot_without_critical_partial_solve_wit_2_pure -> Get_Obj_Slot_without_critical_partial_solve_wit_2_aux.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_3 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> e)
  **  (gos_restore_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )
|--
  “ ((unsigned_last_nbits (prio_pre) (32)) < 63) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ”
  &&  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> e)
  **  (gos_restore_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_4_pure := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |-> e)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
|--
  “ (gos_read_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p ) ”
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (e <= UINT_MAX)) (PreH2 : (e >= 0)) (PreH3 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH4 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |-> e)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
|--
  “ (gos_read_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p ) ”
).

Definition Get_Obj_Slot_without_critical_partial_solve_wit_4_pure_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : (e <= UINT_MAX)) (PreH2 : (e >= 0)) (PreH3 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH4 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |-> e)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
|--
  “ (gos_read_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p ) ”
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_4_aux := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (gos_preserved h )
|--
  “ (gos_read_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p ) ” 
  &&  “ ((unsigned_last_nbits (prio_pre) (32)) < 63) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ”
  &&  (gos_preserved h )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_4 := Get_Obj_Slot_without_critical_partial_solve_wit_4_pure -> Get_Obj_Slot_without_critical_partial_solve_wit_4_aux.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_5 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (PreH1 : ((unsigned_last_nbits (prio_pre) (32)) < 63)) (PreH2 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (gos_restore_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )
|--
  “ ((unsigned_last_nbits (prio_pre) (32)) < 63) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (gos_restore_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_6_pure := 
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (PreH1 : (i < e)) (PreH2 : (p <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= e)) (PreH6 : (e <= UINT_MAX)) (PreH7 : (17 <= i)) (PreH8 : (i <= (gos_limit (xs)))) (PreH9 : ((gos_limit (xs)) <= 255)) (PreH10 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH11 : (gos_safe_observation xs e func_object_pre )) (PreH12 : (gos_no_match xs func_object_pre i )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "endPtr" ) )) # UInt  |-> e)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  (gos_preserved h )
|--
  “ (gos_read_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (i)) ) ”
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (PreH1 : (i <= UINT_MAX)) (PreH2 : (e <= UINT_MAX)) (PreH3 : (i >= 0)) (PreH4 : (e >= 0)) (PreH5 : (i < e)) (PreH6 : (p <> 0)) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre < 63)) (PreH9 : (0 <= e)) (PreH10 : (e <= UINT_MAX)) (PreH11 : (17 <= i)) (PreH12 : (i <= (gos_limit (xs)))) (PreH13 : ((gos_limit (xs)) <= 255)) (PreH14 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH15 : (gos_safe_observation xs e func_object_pre )) (PreH16 : (gos_no_match xs func_object_pre i )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "endPtr" ) )) # UInt  |-> e)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  (gos_preserved h )
|--
  “ (gos_read_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (i)) ) ”
).

Definition Get_Obj_Slot_without_critical_partial_solve_wit_6_pure_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (PreH1 : (i <= UINT_MAX)) (PreH2 : (e <= UINT_MAX)) (PreH3 : (i >= 0)) (PreH4 : (e >= 0)) (PreH5 : (i < e)) (PreH6 : (p <> 0)) (PreH7 : (0 <= prio_pre)) (PreH8 : (prio_pre < 63)) (PreH9 : (0 <= e)) (PreH10 : (e <= UINT_MAX)) (PreH11 : (17 <= i)) (PreH12 : (i <= (gos_limit (xs)))) (PreH13 : ((gos_limit (xs)) <= 255)) (PreH14 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH15 : (gos_safe_observation xs e func_object_pre )) (PreH16 : (gos_no_match xs func_object_pre i )) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "endPtr" ) )) # UInt  |-> e)
  **  ((( &( "i" ) )) # UInt  |-> i)
  **  (gos_preserved h )
|--
  “ (gos_read_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (i)) ) ”
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_6_aux := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (PreH1 : (i < e)) (PreH2 : (p <> 0)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= e)) (PreH6 : (e <= UINT_MAX)) (PreH7 : (17 <= i)) (PreH8 : (i <= (gos_limit (xs)))) (PreH9 : ((gos_limit (xs)) <= 255)) (PreH10 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH11 : (gos_safe_observation xs e func_object_pre )) (PreH12 : (gos_no_match xs func_object_pre i )) ,
  (gos_preserved h )
|--
  “ (gos_read_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (i)) ) ” 
  &&  “ (i < e) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (0 <= e) ” 
  &&  “ (e <= UINT_MAX) ” 
  &&  “ (17 <= i) ” 
  &&  “ (i <= (gos_limit (xs))) ” 
  &&  “ ((gos_limit (xs)) <= 255) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ” 
  &&  “ (gos_safe_observation xs e func_object_pre ) ” 
  &&  “ (gos_no_match xs func_object_pre i ) ”
  &&  (gos_preserved h )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_6 := Get_Obj_Slot_without_critical_partial_solve_wit_6_pure -> Get_Obj_Slot_without_critical_partial_solve_wit_6_aux.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_7 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (PreH1 : (i = j)) (PreH2 : (i < e)) (PreH3 : (p <> 0)) (PreH4 : (0 <= prio_pre)) (PreH5 : (prio_pre < 63)) (PreH6 : (0 <= e)) (PreH7 : (e <= UINT_MAX)) (PreH8 : (17 <= i)) (PreH9 : (i <= (gos_limit (xs)))) (PreH10 : ((gos_limit (xs)) <= 255)) (PreH11 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH12 : (gos_safe_observation xs e func_object_pre )) (PreH13 : (gos_no_match xs func_object_pre i )) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  “ (i = j) ” 
  &&  “ (i < e) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (0 <= e) ” 
  &&  “ (e <= UINT_MAX) ” 
  &&  “ (17 <= i) ” 
  &&  “ (i <= (gos_limit (xs))) ” 
  &&  “ ((gos_limit (xs)) <= 255) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ” 
  &&  “ (gos_safe_observation xs e func_object_pre ) ” 
  &&  “ (gos_no_match xs func_object_pre i ) ”
  &&  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_8 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (PreH1 : ((gos_nth (xs) (j)) = func_object_pre)) (PreH2 : (i = j)) (PreH3 : (i < e)) (PreH4 : (p <> 0)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre < 63)) (PreH7 : (0 <= e)) (PreH8 : (e <= UINT_MAX)) (PreH9 : (17 <= i)) (PreH10 : (i <= (gos_limit (xs)))) (PreH11 : ((gos_limit (xs)) <= 255)) (PreH12 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH13 : (gos_safe_observation xs e func_object_pre )) (PreH14 : (gos_no_match xs func_object_pre i )) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  “ ((gos_nth (xs) (j)) = func_object_pre) ” 
  &&  “ (i = j) ” 
  &&  “ (i < e) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (0 <= e) ” 
  &&  “ (e <= UINT_MAX) ” 
  &&  “ (17 <= i) ” 
  &&  “ (i <= (gos_limit (xs))) ” 
  &&  “ ((gos_limit (xs)) <= 255) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ” 
  &&  “ (gos_safe_observation xs e func_object_pre ) ” 
  &&  “ (gos_no_match xs func_object_pre i ) ”
  &&  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (i)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (i)) )
.

Definition Get_Obj_Slot_without_critical_partial_solve_wit_9 := 
forall (func_object_pre: Z) (prio_pre: Z) (xs: (@list Z)) (e: Z) (p: Z) (h: gos_heap) (i: Z) (j: Z) (PreH1 : ((gos_nth (xs) (j)) <> func_object_pre)) (PreH2 : (i = j)) (PreH3 : (i < e)) (PreH4 : (p <> 0)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre < 63)) (PreH7 : (0 <= e)) (PreH8 : (e <= UINT_MAX)) (PreH9 : (17 <= i)) (PreH10 : (i <= (gos_limit (xs)))) (PreH11 : ((gos_limit (xs)) <= 255)) (PreH12 : (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs )) (PreH13 : (gos_safe_observation xs e func_object_pre )) (PreH14 : (gos_no_match xs func_object_pre i )) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  “ ((gos_nth (xs) (j)) <> func_object_pre) ” 
  &&  “ (i = j) ” 
  &&  “ (i < e) ” 
  &&  “ (p <> 0) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 63) ” 
  &&  “ (0 <= e) ” 
  &&  “ (e <= UINT_MAX) ” 
  &&  “ (17 <= i) ” 
  &&  “ (i <= (gos_limit (xs))) ” 
  &&  “ ((gos_limit (xs)) <= 255) ” 
  &&  “ (gos_input h prio_pre ( &( "OSCSpaceObjectPointer" ) ) ( &( "OSCSpacePrioTbl" ) ) p e func_object_pre xs ) ” 
  &&  “ (gos_safe_observation xs e func_object_pre ) ” 
  &&  “ (gos_no_match xs func_object_pre i ) ”
  &&  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (i)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (i)) )
.

Definition Get_Obj_Slot_without_critical_which_implies_wit_1 := 
(
forall (h: gos_heap) ,
  (gos_exact h )
|--
  (gos_preserved h )
) \/
(
forall (h: gos_heap) ,
  (gos_exact h )
|--
  (gos_preserved h )
).

Definition Get_Obj_Slot_without_critical_which_implies_wit_1_split_goal_spatial := 
forall (h: gos_heap) ,
  (gos_exact h )
|--
  (gos_preserved h )
.

Definition Get_Obj_Slot_without_critical_which_implies_wit_2 := 
(
forall (prio_pre: Z) (e: Z) (h: gos_heap) (PreH1 : (gos_read_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )) ,
  (gos_preserved h )
|--
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> e)
  **  (gos_restore_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )
) \/
(
forall (prio_pre: Z) (e: Z) (h: gos_heap) (PreH1 : (gos_read_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )) ,
  (gos_preserved h )
|--
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> e)
  **  (gos_restore_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )
).

Definition Get_Obj_Slot_without_critical_which_implies_wit_2_split_goal_spatial := 
forall (prio_pre: Z) (e: Z) (h: gos_heap) (PreH1 : (gos_read_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )) ,
  (gos_preserved h )
|--
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> e)
  **  (gos_restore_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )
.

Definition Get_Obj_Slot_without_critical_which_implies_wit_3 := 
(
forall (prio_pre: Z) (e: Z) (h: gos_heap) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> e)
  **  (gos_restore_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )
|--
  (gos_preserved h )
) \/
(
forall (prio_pre: Z) (e: Z) (h: gos_heap) (PreH1 : (e <= UINT_MAX)) (PreH2 : (e >= 0)) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> e)
  **  (gos_restore_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )
|--
  (gos_preserved h )
).

Definition Get_Obj_Slot_without_critical_which_implies_wit_3_split_goal_spatial := 
forall (prio_pre: Z) (e: Z) (h: gos_heap) (PreH1 : (e <= UINT_MAX)) (PreH2 : (e >= 0)) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> e)
  **  (gos_restore_uint h (( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT))) e )
|--
  (gos_preserved h )
.

Definition Get_Obj_Slot_without_critical_which_implies_wit_4 := 
(
forall (prio_pre: Z) (p: Z) (h: gos_heap) (PreH1 : (gos_read_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )) ,
  (gos_preserved h )
|--
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (gos_restore_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )
) \/
(
forall (prio_pre: Z) (p: Z) (h: gos_heap) (PreH1 : (gos_read_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )) ,
  (gos_preserved h )
|--
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (gos_restore_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )
).

Definition Get_Obj_Slot_without_critical_which_implies_wit_4_split_goal_spatial := 
forall (prio_pre: Z) (p: Z) (h: gos_heap) (PreH1 : (gos_read_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )) ,
  (gos_preserved h )
|--
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (gos_restore_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )
.

Definition Get_Obj_Slot_without_critical_which_implies_wit_5 := 
(
forall (prio_pre: Z) (p: Z) (h: gos_heap) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (gos_restore_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )
|--
  (gos_preserved h )
) \/
(
forall (prio_pre: Z) (p: Z) (h: gos_heap) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (gos_restore_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )
|--
  (gos_preserved h )
).

Definition Get_Obj_Slot_without_critical_which_implies_wit_5_split_goal_spatial := 
forall (prio_pre: Z) (p: Z) (h: gos_heap) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (gos_restore_ptr h (( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR))) p )
|--
  (gos_preserved h )
.

Definition Get_Obj_Slot_without_critical_which_implies_wit_6 := 
(
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) (PreH1 : (gos_read_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )) ,
  (gos_preserved h )
|--
  EX (j_2: Z) ,
  “ (j = j_2) ”
  &&  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j_2 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j_2)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j_2 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j_2)) )
) \/
(
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) (PreH1 : (gos_read_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )) ,
  (gos_preserved h )
|--
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
).

Definition Get_Obj_Slot_without_critical_which_implies_wit_6_split_goal_spatial := 
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) (PreH1 : (gos_read_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )) ,
  (gos_preserved h )
|--
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
.

Definition Get_Obj_Slot_without_critical_which_implies_wit_7 := 
(
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  EX (j_2: Z) ,
  “ (j = j_2) ”
  &&  (gos_preserved h )
) \/
(
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  (gos_preserved h )
).

Definition Get_Obj_Slot_without_critical_which_implies_wit_7_split_goal_spatial := 
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  (gos_preserved h )
.

Definition Get_Obj_Slot_without_critical_which_implies_wit_8 := 
(
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  EX (j_2: Z) ,
  “ (j = j_2) ”
  &&  (gos_preserved h )
) \/
(
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  (gos_preserved h )
).

Definition Get_Obj_Slot_without_critical_which_implies_wit_8_split_goal_spatial := 
forall (xs: (@list Z)) (p: Z) (h: gos_heap) (j: Z) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (gos_nth (xs) (j)))
  **  (gos_restore_ptr h &(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (j * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t") (gos_nth (xs) (j)) )
|--
  (gos_preserved h )
.

Module Type VC_Correct.


Axiom proof_of_Get_Obj_Slot_without_critical_safety_wit_1 : Get_Obj_Slot_without_critical_safety_wit_1.
Axiom proof_of_Get_Obj_Slot_without_critical_entail_wit_1 : Get_Obj_Slot_without_critical_entail_wit_1.
Axiom proof_of_Get_Obj_Slot_without_critical_entail_wit_2 : Get_Obj_Slot_without_critical_entail_wit_2.
Axiom proof_of_Get_Obj_Slot_without_critical_return_wit_1 : Get_Obj_Slot_without_critical_return_wit_1.
Axiom proof_of_Get_Obj_Slot_without_critical_return_wit_2 : Get_Obj_Slot_without_critical_return_wit_2.
Axiom proof_of_Get_Obj_Slot_without_critical_return_wit_3 : Get_Obj_Slot_without_critical_return_wit_3.
Axiom proof_of_Get_Obj_Slot_without_critical_return_wit_4 : Get_Obj_Slot_without_critical_return_wit_4.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_1 : Get_Obj_Slot_without_critical_partial_solve_wit_1.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_2_pure : Get_Obj_Slot_without_critical_partial_solve_wit_2_pure.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_2 : Get_Obj_Slot_without_critical_partial_solve_wit_2.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_3 : Get_Obj_Slot_without_critical_partial_solve_wit_3.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_4_pure : Get_Obj_Slot_without_critical_partial_solve_wit_4_pure.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_4 : Get_Obj_Slot_without_critical_partial_solve_wit_4.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_5 : Get_Obj_Slot_without_critical_partial_solve_wit_5.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_6_pure : Get_Obj_Slot_without_critical_partial_solve_wit_6_pure.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_6 : Get_Obj_Slot_without_critical_partial_solve_wit_6.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_7 : Get_Obj_Slot_without_critical_partial_solve_wit_7.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_8 : Get_Obj_Slot_without_critical_partial_solve_wit_8.
Axiom proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_9 : Get_Obj_Slot_without_critical_partial_solve_wit_9.
Axiom proof_of_Get_Obj_Slot_without_critical_which_implies_wit_1 : Get_Obj_Slot_without_critical_which_implies_wit_1.
Axiom proof_of_Get_Obj_Slot_without_critical_which_implies_wit_2 : Get_Obj_Slot_without_critical_which_implies_wit_2.
Axiom proof_of_Get_Obj_Slot_without_critical_which_implies_wit_3 : Get_Obj_Slot_without_critical_which_implies_wit_3.
Axiom proof_of_Get_Obj_Slot_without_critical_which_implies_wit_4 : Get_Obj_Slot_without_critical_which_implies_wit_4.
Axiom proof_of_Get_Obj_Slot_without_critical_which_implies_wit_5 : Get_Obj_Slot_without_critical_which_implies_wit_5.
Axiom proof_of_Get_Obj_Slot_without_critical_which_implies_wit_6 : Get_Obj_Slot_without_critical_which_implies_wit_6.
Axiom proof_of_Get_Obj_Slot_without_critical_which_implies_wit_7 : Get_Obj_Slot_without_critical_which_implies_wit_7.
Axiom proof_of_Get_Obj_Slot_without_critical_which_implies_wit_8 : Get_Obj_Slot_without_critical_which_implies_wit_8.

End VC_Correct.
