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
Require Import SimpleC.EE.osverify_qcp.cases.ucos_get_obj_slot_copy_independent_20261013_lib.
Local Open Scope sac.

(*----- Function Get_Obj_Slot -----*)

Definition Get_Obj_Slot_safety_wit_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (prio_pre >= 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (prio_pre = prio0)) (PreH5 : (func_object_pre = key0)) (PreH6 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH7 : (prio_pre < 63)) (PreH8 : (p <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  “ False ”
.

Definition Get_Obj_Slot_safety_wit_2 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (prio_pre >= 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (prio_pre = prio0)) (PreH5 : (func_object_pre = key0)) (PreH6 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH7 : (prio_pre < 63)) (PreH8 : (p = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ False ”
.

Definition Get_Obj_Slot_safety_wit_3 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (prio_pre < 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (prio_pre = prio0)) (PreH5 : (func_object_pre = key0)) (PreH6 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH7 : (prio_pre >= 63)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "endPtr" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
|--
  “ False ”
.

Definition Get_Obj_Slot_safety_wit_4 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (prio_pre < 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (prio_pre = prio0)) (PreH5 : (func_object_pre = key0)) (PreH6 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH7 : (prio_pre < 63)) (PreH8 : (p <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "endPtr" ) )) # UInt  |-> finish)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Get_Obj_Slot_safety_wit_5 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (prio_pre < 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (prio_pre = prio0)) (PreH5 : (func_object_pre = key0)) (PreH6 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH7 : (prio_pre < 63)) (PreH8 : (p = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "endPtr" ) )) # UInt  |-> finish)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Get_Obj_Slot_safety_wit_6 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (p = 0)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (prio_pre = prio0)) (PreH6 : (func_object_pre = key0)) (PreH7 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH8 : (prio_pre < 63)) (PreH9 : (p <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "endPtr" ) )) # UInt  |-> finish)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  “ False ”
.

Definition Get_Obj_Slot_safety_wit_7 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (prio_pre = prio0)) (PreH6 : (func_object_pre = key0)) (PreH7 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH8 : (prio_pre < 63)) (PreH9 : (p = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "endPtr" ) )) # UInt  |-> finish)
  **  ((( &( "i" ) )) # UInt  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ False ”
.

Definition Get_Obj_Slot_entail_wit_1 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (prio_pre = prio0)) (PreH6 : (func_object_pre = key0)) (PreH7 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH8 : (prio_pre < 63)) (PreH9 : (p <> 0)) ,
  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "func_object" ) )) # Ptr  |-> func_object_pre)
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  “ (0 <= prio0) ” 
  &&  “ (prio0 < 63) ” 
  &&  “ (p <> 0) ” 
  &&  “ (copy_lookup_scan_inv xs key0 finish 17 ) ”
  &&  ((( &( "prio" ) )) # UChar  |-> prio0)
  **  ((( &( "func_object" ) )) # Ptr  |-> key0)
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (finish <= UINT_MAX)) (PreH2 : (finish >= 0)) (PreH3 : (p <> 0)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = prio0)) (PreH8 : (func_object_pre = key0)) (PreH9 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH10 : (prio_pre < 63)) (PreH11 : (p <> 0)) ,
  TT && emp 
|--
  “ (copy_lookup_scan_inv xs func_object_pre finish 17 ) ”
  &&  emp
).

Definition Get_Obj_Slot_entail_wit_1_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (finish <= UINT_MAX)) (PreH2 : (finish >= 0)) (PreH3 : (p <> 0)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = prio0)) (PreH8 : (func_object_pre = key0)) (PreH9 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH10 : (prio_pre < 63)) (PreH11 : (p <> 0)) ,
  (copy_lookup_scan_inv xs func_object_pre finish 17 )
.

Definition Get_Obj_Slot_entail_wit_2 := 
(
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (i: Z) (PreH1 : (i < finish)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  EX (v: Z) ,
  “ (0 <= prio0) ” 
  &&  “ (prio0 < 63) ” 
  &&  “ (p <> 0) ” 
  &&  “ (copy_lookup_scan_inv xs key0 finish i ) ” 
  &&  “ (i < finish) ” 
  &&  “ (i < 255) ” 
  &&  “ (v = (copy_lookup_at (xs) (i))) ”
  &&  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
) \/
(
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (i: Z) (PreH1 : (i < finish)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) ,
  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  “ (i < 255) ”
  &&  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_lookup_at (xs) (i)))
).

Definition Get_Obj_Slot_entail_wit_2_split_goal_1 := 
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (i: Z) (PreH1 : (i < finish)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) ,
  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  “ (i < 255) ”
.

Definition Get_Obj_Slot_entail_wit_2_split_goal_spatial := 
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (i: Z) (PreH1 : (i < finish)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) ,
  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_lookup_at (xs) (i)))
.

Definition Get_Obj_Slot_entail_wit_3 := 
(
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (v: Z) (i: Z) (PreH1 : (v <> key0)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) (PreH6 : (i < finish)) (PreH7 : (i < 255)) (PreH8 : (v = (copy_lookup_at (xs) (i)))) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
|--
  “ (0 <= prio0) ” 
  &&  “ (prio0 < 63) ” 
  &&  “ (p <> 0) ” 
  &&  “ (copy_lookup_scan_inv xs key0 finish (i + 1 ) ) ”
  &&  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
) \/
(
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (v: Z) (i: Z) (PreH1 : (v <> key0)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) (PreH6 : (i < finish)) (PreH7 : (i < 255)) (PreH8 : (v = (copy_lookup_at (xs) (i)))) ,
  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
|--
  “ (copy_lookup_scan_inv xs key0 finish (i + 1 ) ) ”
  &&  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
).

Definition Get_Obj_Slot_entail_wit_3_split_goal_1 := 
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (v: Z) (i: Z) (PreH1 : (v <> key0)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) (PreH6 : (i < finish)) (PreH7 : (i < 255)) (PreH8 : (v = (copy_lookup_at (xs) (i)))) ,
  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
|--
  “ (copy_lookup_scan_inv xs key0 finish (i + 1 ) ) ”
.

Definition Get_Obj_Slot_entail_wit_3_split_goal_spatial := 
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (v: Z) (i: Z) (PreH1 : (v <> key0)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) (PreH6 : (i < finish)) (PreH7 : (i < 255)) (PreH8 : (v = (copy_lookup_at (xs) (i)))) ,
  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
|--
  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
.

Definition Get_Obj_Slot_return_wit_1 := 
(
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (i: Z) (PreH1 : (i >= finish)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
|--
  “ (copy_lookup_result prio0 p finish key0 xs 0 ) ” 
  &&  “ (prio0 < 63) ” 
  &&  “ (p <> 0) ”
  &&  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
) \/
(
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (i: Z) (PreH1 : (i >= finish)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) ,
  TT && emp 
|--
  “ (copy_lookup_result prio0 p finish key0 xs 0 ) ”
  &&  emp
).

Definition Get_Obj_Slot_return_wit_1_split_goal_1 := 
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (i: Z) (PreH1 : (i >= finish)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) ,
  (copy_lookup_result prio0 p finish key0 xs 0 )
.

Definition Get_Obj_Slot_return_wit_2 := 
(
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (v: Z) (i: Z) (PreH1 : (v = key0)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) (PreH6 : (i < finish)) (PreH7 : (i < 255)) (PreH8 : (v = (copy_lookup_at (xs) (i)))) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
|--
  “ (copy_lookup_result prio0 p finish key0 xs i ) ” 
  &&  “ (prio0 < 63) ” 
  &&  “ (p <> 0) ”
  &&  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
  **  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
) \/
(
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (v: Z) (i: Z) (PreH1 : (v = key0)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) (PreH6 : (i < finish)) (PreH7 : (i < 255)) (PreH8 : (v = (copy_lookup_at (xs) (i)))) ,
  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
|--
  “ (copy_lookup_result prio0 p finish key0 xs i ) ”
  &&  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
).

Definition Get_Obj_Slot_return_wit_2_split_goal_1 := 
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (v: Z) (i: Z) (PreH1 : (v = key0)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) (PreH6 : (i < finish)) (PreH7 : (i < 255)) (PreH8 : (v = (copy_lookup_at (xs) (i)))) ,
  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
|--
  “ (copy_lookup_result prio0 p finish key0 xs i ) ”
.

Definition Get_Obj_Slot_return_wit_2_split_goal_spatial := 
forall (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (v: Z) (i: Z) (PreH1 : (v = key0)) (PreH2 : (0 <= prio0)) (PreH3 : (prio0 < 63)) (PreH4 : (p <> 0)) (PreH5 : (copy_lookup_scan_inv xs key0 finish i )) (PreH6 : (i < finish)) (PreH7 : (i < 255)) (PreH8 : (v = (copy_lookup_at (xs) (i)))) ,
  (copy_lookup_cells_hole p sizeof( "slot" ) 17 xs i )
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (i * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> v)
|--
  (copy_lookup_cells p sizeof( "slot" ) 17 xs )
.

Definition Get_Obj_Slot_return_wit_3 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (p = 0)) (PreH2 : (prio_pre < 63)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre <= 255)) (PreH5 : (prio_pre = prio0)) (PreH6 : (func_object_pre = key0)) (PreH7 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH8 : (prio_pre < 63)) (PreH9 : (p = 0)) ,
  (((( &( "OSCSpaceObjectPointer" ) ) + (prio_pre * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (copy_lookup_result prio0 p finish key0 xs 0 ) ” 
  &&  “ (prio0 < 63) ” 
  &&  “ (p = 0) ”
  &&  (((( &( "OSCSpaceObjectPointer" ) ) + (prio0 * sizeof(UINT)))) # UInt  |-> finish)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio0 * sizeof(PTR)))) # Ptr  |-> p)
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (finish <= UINT_MAX)) (PreH2 : (finish >= 0)) (PreH3 : (p = 0)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = prio0)) (PreH8 : (func_object_pre = key0)) (PreH9 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH10 : (prio_pre < 63)) (PreH11 : (p = 0)) ,
  TT && emp 
|--
  “ (copy_lookup_result prio_pre 0 finish func_object_pre xs 0 ) ”
  &&  emp
).

Definition Get_Obj_Slot_return_wit_3_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (finish <= UINT_MAX)) (PreH2 : (finish >= 0)) (PreH3 : (p = 0)) (PreH4 : (prio_pre < 63)) (PreH5 : (0 <= prio_pre)) (PreH6 : (prio_pre <= 255)) (PreH7 : (prio_pre = prio0)) (PreH8 : (func_object_pre = key0)) (PreH9 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH10 : (prio_pre < 63)) (PreH11 : (p = 0)) ,
  (copy_lookup_result prio_pre 0 finish func_object_pre xs 0 )
.

Definition Get_Obj_Slot_return_wit_4 := 
(
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (prio_pre >= 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (prio_pre = prio0)) (PreH5 : (func_object_pre = key0)) (PreH6 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH7 : (prio_pre >= 63)) ,
  TT && emp 
|--
  “ (copy_lookup_result prio0 p finish key0 xs 42 ) ” 
  &&  “ (prio0 >= 63) ”
  &&  emp
) \/
(
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (prio_pre >= 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (prio_pre = prio0)) (PreH5 : (func_object_pre = key0)) (PreH6 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH7 : (prio_pre >= 63)) ,
  TT && emp 
|--
  “ (copy_lookup_result prio_pre p finish func_object_pre xs 42 ) ”
  &&  emp
).

Definition Get_Obj_Slot_return_wit_4_split_goal_1 := 
forall (func_object_pre: Z) (prio_pre: Z) (key0: Z) (prio0: Z) (xs: (@list Z)) (finish: Z) (p: Z) (PreH1 : (prio_pre >= 63)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre <= 255)) (PreH4 : (prio_pre = prio0)) (PreH5 : (func_object_pre = key0)) (PreH6 : (copy_lookup_input_safe prio_pre p finish func_object_pre xs )) (PreH7 : (prio_pre >= 63)) ,
  (copy_lookup_result prio_pre p finish func_object_pre xs 42 )
.

Module Type VC_Correct.


Axiom proof_of_Get_Obj_Slot_safety_wit_1 : Get_Obj_Slot_safety_wit_1.
Axiom proof_of_Get_Obj_Slot_safety_wit_2 : Get_Obj_Slot_safety_wit_2.
Axiom proof_of_Get_Obj_Slot_safety_wit_3 : Get_Obj_Slot_safety_wit_3.
Axiom proof_of_Get_Obj_Slot_safety_wit_4 : Get_Obj_Slot_safety_wit_4.
Axiom proof_of_Get_Obj_Slot_safety_wit_5 : Get_Obj_Slot_safety_wit_5.
Axiom proof_of_Get_Obj_Slot_safety_wit_6 : Get_Obj_Slot_safety_wit_6.
Axiom proof_of_Get_Obj_Slot_safety_wit_7 : Get_Obj_Slot_safety_wit_7.
Axiom proof_of_Get_Obj_Slot_entail_wit_1 : Get_Obj_Slot_entail_wit_1.
Axiom proof_of_Get_Obj_Slot_entail_wit_2 : Get_Obj_Slot_entail_wit_2.
Axiom proof_of_Get_Obj_Slot_entail_wit_3 : Get_Obj_Slot_entail_wit_3.
Axiom proof_of_Get_Obj_Slot_return_wit_1 : Get_Obj_Slot_return_wit_1.
Axiom proof_of_Get_Obj_Slot_return_wit_2 : Get_Obj_Slot_return_wit_2.
Axiom proof_of_Get_Obj_Slot_return_wit_3 : Get_Obj_Slot_return_wit_3.
Axiom proof_of_Get_Obj_Slot_return_wit_4 : Get_Obj_Slot_return_wit_4.

End VC_Correct.
