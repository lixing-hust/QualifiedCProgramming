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
Require Import SimpleC.EE.osverify_qcp.cases.ucos_cnode_copy_independent_20261013_lib.
Local Open Scope sac.

(*----- Function ucos_CNode_Copy -----*)

Definition ucos_CNode_Copy_safety_wit_1 := 
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (destTask_Prio_pre = d0)) (PreH2 : (srcTask_Prio_pre = s0)) (PreH3 : (func_capability_pre = f0)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "idx" ) )) # UInt  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (copy_heap h )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Copy_safety_wit_2 := 
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (destTask_Prio_pre = d0)) (PreH2 : (srcTask_Prio_pre = s0)) (PreH3 : (func_capability_pre = f0)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |-> 0)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "idx" ) )) # UInt  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (copy_heap h )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Copy_safety_wit_3 := 
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (func_capability_pre < 255)) (PreH2 : (destTask_Prio_pre = d0)) (PreH3 : (srcTask_Prio_pre = s0)) (PreH4 : (func_capability_pre = f0)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  ((( &( "cap2" ) )) # Ptr  |-> 0)
  **  ((( &( "cap1" ) )) # Ptr  |-> 0)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "idx" ) )) # UInt  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (copy_heap h )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition ucos_CNode_Copy_safety_wit_4 := 
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = d0)) (PreH4 : (srcTask_Prio_pre = s0)) (PreH5 : (func_capability_pre = f0)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  ((( &( "cap2" ) )) # Ptr  |-> 0)
  **  ((( &( "cap1" ) )) # Ptr  |-> 0)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "idx" ) )) # UInt  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (copy_heap h )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition ucos_CNode_Copy_safety_wit_5 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (cap1 = 0)) (PreH6 : (cap2 = 0)) (PreH7 : (pCSpace1 = (copy_table (a) (d0)))) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> d0)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> s0)
  **  ((( &( "func_capability" ) )) # UInt  |-> f0)
  **  ((( &( "cap1" ) )) # Ptr  |-> cap1)
  **  ((( &( "cap2" ) )) # Ptr  |-> cap2)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> pCSpace1)
  **  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> (copy_table (a) (s0)))
  **  ((( &( "idx" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Copy_safety_wit_6 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : (pCSpace1 <> 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (cap1 = 0)) (PreH7 : (cap2 = 0)) (PreH8 : (pCSpace1 = (copy_table (a) (d0)))) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> d0)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> s0)
  **  ((( &( "func_capability" ) )) # UInt  |-> f0)
  **  ((( &( "cap1" ) )) # Ptr  |-> cap1)
  **  ((( &( "cap2" ) )) # Ptr  |-> cap2)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> pCSpace1)
  **  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> (copy_table (a) (s0)))
  **  ((( &( "idx" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Copy_entail_wit_1 := 
(
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = d0)) (PreH5 : (srcTask_Prio_pre = s0)) (PreH6 : (func_capability_pre = f0)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (copy_heap h )
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> d0)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> s0)
  **  ((( &( "func_capability" ) )) # UInt  |-> f0)
  **  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (d0)))
) \/
(
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = d0)) (PreH5 : (srcTask_Prio_pre = s0)) (PreH6 : (func_capability_pre = f0)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  (copy_heap h )
|--
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (d0)))
).

Definition ucos_CNode_Copy_entail_wit_1_split_goal_spatial := 
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = d0)) (PreH5 : (srcTask_Prio_pre = s0)) (PreH6 : (func_capability_pre = f0)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  (copy_heap h )
|--
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (d0)))
.

Definition ucos_CNode_Copy_entail_wit_2 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (cap1 = 0)) (PreH6 : (cap2 = 0)) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (d0)))
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (cap1 = 0) ” 
  &&  “ (cap2 = 0) ” 
  &&  “ ((copy_table (a) (d0)) = (copy_table (a) (d0))) ”
  &&  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (cap1 = 0)) (PreH6 : (cap2 = 0)) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (d0)))
|--
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
).

Definition ucos_CNode_Copy_entail_wit_2_split_goal_spatial := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (cap1 = 0)) (PreH6 : (cap2 = 0)) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (d0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (d0)))
|--
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
.

Definition ucos_CNode_Copy_entail_wit_3 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : ((copy_table (a) (s0)) <> 0)) (PreH2 : (pCSpace1 <> 0)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (cap1 = 0)) (PreH8 : (cap2 = 0)) (PreH9 : (pCSpace1 = (copy_table (a) (d0)))) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ ((copy_table (a) (s0)) = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ ((copy_table (a) (s0)) <> 0) ” 
  &&  “ (&(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability") = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (&(((&(((copy_table (a) (s0)))  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability") = &(((&(((copy_table (a) (s0)))  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ”
  &&  (copy_hole h &(((&(((copy_table (a) (s0)))  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type") )
  **  ((&(((&(((copy_table (a) (s0)))  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : ((copy_table (a) (s0)) <> 0)) (PreH2 : (pCSpace1 <> 0)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (cap1 = 0)) (PreH8 : (cap2 = 0)) (PreH9 : (pCSpace1 = (copy_table (a) (d0)))) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
|--
  (copy_hole h &(((&(((copy_table (a) (s0)))  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type") )
  **  ((&(((&(((copy_table (a) (s0)))  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
).

Definition ucos_CNode_Copy_entail_wit_3_split_goal_spatial := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : ((copy_table (a) (s0)) <> 0)) (PreH2 : (pCSpace1 <> 0)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (cap1 = 0)) (PreH8 : (cap2 = 0)) (PreH9 : (pCSpace1 = (copy_table (a) (d0)))) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
|--
  (copy_hole h &(((&(((copy_table (a) (s0)))  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type") )
  **  ((&(((&(((copy_table (a) (s0)))  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
.

Definition ucos_CNode_Copy_entail_wit_4 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ”
  &&  (copy_hole h &((cap1)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap1)  # "cap" ->ₛ "cap_type")) # UInt  |->_)
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <= UINT_MAX)) (PreH2 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) >= 0)) (PreH3 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH4 : (f0 < 255)) (PreH5 : (d0 < 64)) (PreH6 : (s0 < 64)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH8 : (pCSpace1 = (copy_table (a) (d0)))) (PreH9 : (pCSpace2 = (copy_table (a) (s0)))) (PreH10 : (pCSpace1 <> 0)) (PreH11 : (pCSpace2 <> 0)) (PreH12 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH13 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (x: Z) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ”
  &&  ((&((cap1)  # "cap" ->ₛ "cap_type")) # UInt  |-> x)
  **  (copy_hole h &((cap1)  # "cap" ->ₛ "cap_type") )
).

Definition ucos_CNode_Copy_entail_wit_5 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) ,
  (copy_hole h &((cap1)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap1)  # "cap" ->ₛ "cap_type")) # UInt  |-> 1)
|--
  (“ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ”
  &&  (copy_hole (copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1)) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0))))))
  ||
  (“ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ”
  &&  (copy_two_holes (copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1)) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_))
.

Definition ucos_CNode_Copy_entail_wit_6_1 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH12 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content"))) ,
  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  (copy_hole (copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1)) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") )
|--
  (“ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) ”
  &&  (copy_hole (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0))))))
  ||
  (“ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) ”
  &&  (copy_two_holes (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_))
.

Definition ucos_CNode_Copy_entail_wit_6_2 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH12 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content"))) ,
  (copy_two_holes (copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1)) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  (“ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) ”
  &&  (copy_hole (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0))))))
  ||
  (“ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) ”
  &&  (copy_two_holes (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_))
.

Definition ucos_CNode_Copy_entail_wit_7 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH2 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <> 1)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (pCSpace1 = (copy_table (a) (d0)))) (PreH8 : (pCSpace2 = (copy_table (a) (s0)))) (PreH9 : (pCSpace1 <> 0)) (PreH10 : (pCSpace2 <> 0)) (PreH11 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ”
  &&  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <= UINT_MAX)) (PreH2 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) >= 0)) (PreH3 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH4 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <> 1)) (PreH5 : (f0 < 255)) (PreH6 : (d0 < 64)) (PreH7 : (s0 < 64)) (PreH8 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH9 : (pCSpace1 = (copy_table (a) (d0)))) (PreH10 : (pCSpace2 = (copy_table (a) (s0)))) (PreH11 : (pCSpace1 <> 0)) (PreH12 : (pCSpace2 <> 0)) (PreH13 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH14 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
).

Definition ucos_CNode_Copy_entail_wit_7_split_goal_spatial := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <= UINT_MAX)) (PreH2 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) >= 0)) (PreH3 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH4 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <> 1)) (PreH5 : (f0 < 255)) (PreH6 : (d0 < 64)) (PreH7 : (s0 < 64)) (PreH8 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH9 : (pCSpace1 = (copy_table (a) (d0)))) (PreH10 : (pCSpace2 = (copy_table (a) (s0)))) (PreH11 : (pCSpace1 <> 0)) (PreH12 : (pCSpace2 <> 0)) (PreH13 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH14 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
.

Definition ucos_CNode_Copy_entail_wit_8 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (xs: (@list Z)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ ((copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (0 <= d0) ” 
  &&  “ (d0 <= 255) ” 
  &&  “ (copy_lookup_agrees a d0 xs ) ” 
  &&  “ (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) xs ) ” 
  &&  “ (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs ) ”
  &&  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
  **  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (xs: (@list Z)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (0 <= d0) ” 
  &&  “ (d0 <= 255) ” 
  &&  “ (copy_lookup_agrees a d0 xs ) ” 
  &&  “ (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) xs ) ” 
  &&  “ (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs ) ”
  &&  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
  **  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
).

Definition ucos_CNode_Copy_entail_wit_9 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (xs: (@list Z)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (retval: Z) (PreH1 : (copy_lookup_result d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs retval )) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (0 <= d0)) (PreH15 : (d0 <= 255)) (PreH16 : (copy_lookup_agrees a d0 xs )) (PreH17 : (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs )) (PreH18 : (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )) ,
  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
  **  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_lookup a d0 lookup_object retval ) ”
  &&  (copy_heap h )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (xs: (@list Z)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (retval: Z) (PreH1 : (copy_lookup_result d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs retval )) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (0 <= d0)) (PreH15 : (d0 <= 255)) (PreH16 : (copy_lookup_agrees a d0 xs )) (PreH17 : (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs )) (PreH18 : (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )) ,
  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
  **  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
|--
  “ (copy_lookup a d0 lookup_object retval ) ”
  &&  (copy_heap h )
).

Definition ucos_CNode_Copy_entail_wit_9_split_goal_1 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (xs: (@list Z)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (retval: Z) (PreH1 : (copy_lookup_result d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs retval )) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (0 <= d0)) (PreH15 : (d0 <= 255)) (PreH16 : (copy_lookup_agrees a d0 xs )) (PreH17 : (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs )) (PreH18 : (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )) ,
  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
  **  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
|--
  “ (copy_lookup a d0 lookup_object retval ) ”
.

Definition ucos_CNode_Copy_entail_wit_9_split_goal_spatial := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (xs: (@list Z)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (retval: Z) (PreH1 : (copy_lookup_result d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs retval )) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (0 <= d0)) (PreH15 : (d0 <= 255)) (PreH16 : (copy_lookup_agrees a d0 xs )) (PreH17 : (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs )) (PreH18 : (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )) ,
  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
  **  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
|--
  (copy_heap h )
.

Definition ucos_CNode_Copy_entail_wit_10 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (idx = 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (copy_lookup a d0 lookup_object idx )) ,
  (copy_heap h )
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (idx = 0) ” 
  &&  “ (copy_lookup a d0 lookup_object 0 ) ”
  &&  (copy_hole h (( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT))) )
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT)))) # UInt  |-> (copy_counter (a) (d0)))
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (idx = 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (copy_lookup a d0 lookup_object idx )) ,
  (copy_heap h )
|--
  (copy_hole h (( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT))) )
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT)))) # UInt  |-> (copy_counter (a) (d0)))
).

Definition ucos_CNode_Copy_entail_wit_10_split_goal_spatial := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (idx = 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (copy_lookup a d0 lookup_object idx )) ,
  (copy_heap h )
|--
  (copy_hole h (( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT))) )
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT)))) # UInt  |-> (copy_counter (a) (d0)))
.

Definition ucos_CNode_Copy_entail_wit_11_1 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : ((copy_counter (a) (d0)) < 255)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (idx = 0)) (PreH15 : (copy_lookup a d0 lookup_object 0 )) ,
  (copy_hole h (( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT))) )
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT)))) # UInt  |-> ((copy_counter (a) (d0)) + 1 ))
|--
  EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object (copy_counter (a) (d0)) ) ”
  &&  (copy_heap hc )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (((copy_counter (a) (d0)) + 1 ) <= UINT_MAX)) (PreH2 : (((copy_counter (a) (d0)) + 1 ) >= 0)) (PreH3 : ((copy_counter (a) (d0)) < 255)) (PreH4 : (f0 < 255)) (PreH5 : (d0 < 64)) (PreH6 : (s0 < 64)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH8 : (pCSpace1 = (copy_table (a) (d0)))) (PreH9 : (pCSpace2 = (copy_table (a) (s0)))) (PreH10 : (pCSpace1 <> 0)) (PreH11 : (pCSpace2 <> 0)) (PreH12 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH13 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH14 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH15 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH16 : (idx = 0)) (PreH17 : (copy_lookup a d0 lookup_object 0 )) ,
  (copy_hole h (( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT))) )
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT)))) # UInt  |-> ((copy_counter (a) (d0)) + 1 ))
|--
  EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object (copy_counter (a) (d0)) ) ”
  &&  (copy_heap hc )
).

Definition ucos_CNode_Copy_entail_wit_11_2 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (idx <> 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (copy_lookup a d0 lookup_object idx )) ,
  (copy_heap h )
|--
  EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ”
  &&  (copy_heap hc )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (idx <> 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (copy_lookup a d0 lookup_object idx )) ,
  TT && emp 
|--
  “ (copy_allocation_state h h a ( &( "OSCSpaceObjectPointer" ) ) d0 (copy_pointer ((copy_slots (a) (pCSpace2) (f0)))) idx ) ”
  &&  emp
).

Definition ucos_CNode_Copy_entail_wit_11_2_split_goal_1 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (idx <> 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (copy_lookup a d0 lookup_object idx )) ,
  (copy_allocation_state h h a ( &( "OSCSpaceObjectPointer" ) ) d0 (copy_pointer ((copy_slots (a) (pCSpace2) (f0)))) idx )
.

Definition ucos_CNode_Copy_entail_wit_12 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc_2: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc_2 a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) ,
  (copy_heap hc_2 )
|--
  EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (&(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability") = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ”
  &&  (copy_hole hc &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type") )
  **  ((&(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc_2: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc_2 a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) ,
  (copy_heap hc_2 )
|--
  EX (x: Z)  (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ”
  &&  ((&(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> x)
  **  (copy_hole hc &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type") )
).

Definition ucos_CNode_Copy_entail_wit_13 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc_2: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc_2 a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) ,
  (copy_hole hc_2 &((cap1)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap1)  # "cap" ->ₛ "cap_type")) # UInt  |-> 2)
|--
  (EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ”
  &&  (copy_two_holes (copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2)) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_))
  ||
  (EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ”
  &&  (copy_hole (copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2)) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0))))))
.

Definition ucos_CNode_Copy_entail_wit_14_1 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc_2: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc_2 a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right"))) ,
  (copy_two_holes (copy_put (hc_2) (&((cap1)  # "cap" ->ₛ "cap_type")) (2)) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  (EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) ”
  &&  (copy_two_holes (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_))
  ||
  (EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) ”
  &&  (copy_hole (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))))
.

Definition ucos_CNode_Copy_entail_wit_14_2 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc_2: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc_2 a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right"))) ,
  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  (copy_hole (copy_put (hc_2) (&((cap1)  # "cap" ->ₛ "cap_type")) (2)) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") )
|--
  (EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) ”
  &&  (copy_two_holes (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_))
  ||
  (EX (hc: (@list copy_cell)) ,
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) ”
  &&  (copy_hole (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))))
.

Definition ucos_CNode_Copy_return_wit_1 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH12 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right"))) ,
  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  (copy_hole (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 0 ) ”
  &&  (copy_heap hout )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <= UINT_MAX)) (PreH2 : ((copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) >= 0)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (pCSpace1 = (copy_table (a) (d0)))) (PreH8 : (pCSpace2 = (copy_table (a) (s0)))) (PreH9 : (pCSpace1 <> 0)) (PreH10 : (pCSpace2 <> 0)) (PreH11 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH13 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right"))) ,
  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  (copy_hole (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 0 ) ”
  &&  (copy_heap hout )
).

Definition ucos_CNode_Copy_return_wit_2 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH12 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right"))) ,
  (copy_two_holes (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 0 ) ”
  &&  (copy_heap hout )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <= UINT_MAX)) (PreH2 : ((copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) >= 0)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (pCSpace1 = (copy_table (a) (d0)))) (PreH8 : (pCSpace2 = (copy_table (a) (s0)))) (PreH9 : (pCSpace1 <> 0)) (PreH10 : (pCSpace2 <> 0)) (PreH11 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH13 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right"))) ,
  (copy_two_holes (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 0 ) ”
  &&  (copy_heap hout )
).

Definition ucos_CNode_Copy_return_wit_3 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <> 2)) (PreH2 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <> 1)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (pCSpace1 = (copy_table (a) (d0)))) (PreH8 : (pCSpace2 = (copy_table (a) (s0)))) (PreH9 : (pCSpace1 <> 0)) (PreH10 : (pCSpace2 <> 0)) (PreH11 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <= UINT_MAX)) (PreH2 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) >= 0)) (PreH3 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <> 2)) (PreH4 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) <> 1)) (PreH5 : (f0 < 255)) (PreH6 : (d0 < 64)) (PreH7 : (s0 < 64)) (PreH8 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH9 : (pCSpace1 = (copy_table (a) (d0)))) (PreH10 : (pCSpace2 = (copy_table (a) (s0)))) (PreH11 : (pCSpace1 <> 0)) (PreH12 : (pCSpace2 <> 0)) (PreH13 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH14 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) ,
  (copy_hole h &((cap2)  # "cap" ->ₛ "cap_type") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_type")) # UInt  |-> (copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
).

Definition ucos_CNode_Copy_return_wit_4 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t"))) ,
  (copy_two_holes (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 0 ) ”
  &&  (copy_heap hout )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") <> &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t"))) ,
  (copy_two_holes (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 0 ) ”
  &&  (copy_heap hout )
).

Definition ucos_CNode_Copy_return_wit_5 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t"))) ,
  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  (copy_hole (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 0 ) ”
  &&  (copy_heap hout )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t"))) ,
  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
  **  (copy_hole (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 0 ) ”
  &&  (copy_heap hout )
).

Definition ucos_CNode_Copy_return_wit_6 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : ((copy_counter (a) (d0)) >= 255)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (pCSpace1 = (copy_table (a) (d0)))) (PreH7 : (pCSpace2 = (copy_table (a) (s0)))) (PreH8 : (pCSpace1 <> 0)) (PreH9 : (pCSpace2 <> 0)) (PreH10 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH12 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH13 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH14 : (idx = 0)) (PreH15 : (copy_lookup a d0 lookup_object 0 )) ,
  (copy_hole h (( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT))) )
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT)))) # UInt  |-> (copy_counter (a) (d0)))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 2 ) ”
  &&  (copy_heap hout )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (idx: Z) (PreH1 : ((copy_counter (a) (d0)) <= UINT_MAX)) (PreH2 : ((copy_counter (a) (d0)) >= 0)) (PreH3 : ((copy_counter (a) (d0)) >= 255)) (PreH4 : (f0 < 255)) (PreH5 : (d0 < 64)) (PreH6 : (s0 < 64)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH8 : (pCSpace1 = (copy_table (a) (d0)))) (PreH9 : (pCSpace2 = (copy_table (a) (s0)))) (PreH10 : (pCSpace1 <> 0)) (PreH11 : (pCSpace2 <> 0)) (PreH12 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH13 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH14 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH15 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH16 : (idx = 0)) (PreH17 : (copy_lookup a d0 lookup_object 0 )) ,
  (copy_hole h (( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT))) )
  **  (((( &( "OSCSpaceObjectPointer" ) ) + (d0 * sizeof(UINT)))) # UInt  |-> (copy_counter (a) (d0)))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 2 ) ”
  &&  (copy_heap hout )
).

Definition ucos_CNode_Copy_return_wit_7 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : (pCSpace1 = 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (cap1 = 0)) (PreH7 : (cap2 = 0)) (PreH8 : (pCSpace1 = (copy_table (a) (d0)))) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : (pCSpace1 = 0)) (PreH2 : (f0 < 255)) (PreH3 : (d0 < 64)) (PreH4 : (s0 < 64)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH6 : (cap1 = 0)) (PreH7 : (cap2 = 0)) (PreH8 : (pCSpace1 = (copy_table (a) (d0)))) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
).

Definition ucos_CNode_Copy_return_wit_8 := 
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : ((copy_table (a) (s0)) = 0)) (PreH2 : (pCSpace1 <> 0)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (cap1 = 0)) (PreH8 : (cap2 = 0)) (PreH9 : (pCSpace1 = (copy_table (a) (d0)))) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
) \/
(
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (cap1: Z) (cap2: Z) (pCSpace1: Z) (PreH1 : ((copy_table (a) (s0)) = 0)) (PreH2 : (pCSpace1 <> 0)) (PreH3 : (f0 < 255)) (PreH4 : (d0 < 64)) (PreH5 : (s0 < 64)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH7 : (cap1 = 0)) (PreH8 : (cap2 = 0)) (PreH9 : (pCSpace1 = (copy_table (a) (d0)))) ,
  (copy_hole h (( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR))) )
  **  (((( &( "OSCSpacePrioTbl" ) ) + (s0 * sizeof(PTR)))) # Ptr  |-> (copy_table (a) (s0)))
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
).

Definition ucos_CNode_Copy_return_wit_9 := 
(
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = d0)) (PreH4 : (srcTask_Prio_pre = s0)) (PreH5 : (func_capability_pre = f0)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  (copy_heap h )
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
) \/
(
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = d0)) (PreH4 : (srcTask_Prio_pre = s0)) (PreH5 : (func_capability_pre = f0)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  TT && emp 
|--
  “ (copy_post h h a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre 6 ) ”
  &&  emp
).

Definition ucos_CNode_Copy_return_wit_9_split_goal_1 := 
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = d0)) (PreH4 : (srcTask_Prio_pre = s0)) (PreH5 : (func_capability_pre = f0)) (PreH6 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  (copy_post h h a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre 6 )
.

Definition ucos_CNode_Copy_return_wit_10 := 
(
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = d0)) (PreH5 : (srcTask_Prio_pre = s0)) (PreH6 : (func_capability_pre = f0)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  (copy_heap h )
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
) \/
(
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = d0)) (PreH5 : (srcTask_Prio_pre = s0)) (PreH6 : (func_capability_pre = f0)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  TT && emp 
|--
  “ (copy_post h h a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre 6 ) ”
  &&  emp
).

Definition ucos_CNode_Copy_return_wit_10_split_goal_1 := 
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = d0)) (PreH5 : (srcTask_Prio_pre = s0)) (PreH6 : (func_capability_pre = f0)) (PreH7 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  (copy_post h h a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre 6 )
.

Definition ucos_CNode_Copy_return_wit_11 := 
(
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = d0)) (PreH3 : (srcTask_Prio_pre = s0)) (PreH4 : (func_capability_pre = f0)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  (copy_heap h )
|--
  EX (hout: (@list copy_cell)) ,
  “ (copy_post h hout a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) d0 s0 f0 6 ) ”
  &&  (copy_heap hout )
) \/
(
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = d0)) (PreH3 : (srcTask_Prio_pre = s0)) (PreH4 : (func_capability_pre = f0)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  TT && emp 
|--
  “ (copy_post h h a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre 6 ) ”
  &&  emp
).

Definition ucos_CNode_Copy_return_wit_11_split_goal_1 := 
forall (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = d0)) (PreH3 : (srcTask_Prio_pre = s0)) (PreH4 : (func_capability_pre = f0)) (PreH5 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre )) ,
  (copy_post h h a ( &( "OSCSpaceObjectPointer" ) ) sizeof( "slot" ) destTask_Prio_pre srcTask_Prio_pre func_capability_pre 6 )
.

Definition ucos_CNode_Copy_partial_solve_wit_1 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH12 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content"))) ,
  (copy_hole (copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1)) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ”
  &&  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  (copy_hole (copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1)) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content") )
.

Definition ucos_CNode_Copy_partial_solve_wit_2 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1)) (PreH12 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right"))) ,
  (copy_hole (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (copy_word1 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 1) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) ”
  &&  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_)
  **  (copy_hole (copy_put ((copy_put (h) (&((cap1)  # "cap" ->ₛ "cap_type")) (1))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_content")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "category" .ₛ "category_right") )
.

Definition ucos_CNode_Copy_partial_solve_wit_3_pure := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (xs: (@list Z)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (0 <= d0)) (PreH14 : (d0 <= 255)) (PreH15 : (copy_lookup_agrees a d0 xs )) (PreH16 : (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs )) (PreH17 : (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> d0)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> s0)
  **  ((( &( "func_capability" ) )) # UInt  |-> f0)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> pCSpace1)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> pCSpace2)
  **  ((( &( "cap1" ) )) # Ptr  |-> cap1)
  **  ((( &( "cap2" ) )) # Ptr  |-> cap2)
  **  ((( &( "lookup_object" ) )) # Ptr  |-> lookup_object)
  **  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
  **  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
  **  ((( &( "idx" ) )) # UInt  |->_)
|--
  “ (0 <= d0) ” 
  &&  “ (d0 <= 255) ” 
  &&  “ (d0 = d0) ” 
  &&  “ (lookup_object = lookup_object) ” 
  &&  “ (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs ) ”
.

Definition ucos_CNode_Copy_partial_solve_wit_3_aux := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (xs: (@list Z)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (0 <= d0)) (PreH14 : (d0 <= 255)) (PreH15 : (copy_lookup_agrees a d0 xs )) (PreH16 : (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs )) (PreH17 : (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )) ,
  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
  **  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
|--
  “ (0 <= d0) ” 
  &&  “ (d0 <= 255) ” 
  &&  “ (d0 = d0) ” 
  &&  “ (lookup_object = lookup_object) ” 
  &&  “ (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs ) ” 
  &&  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (0 <= d0) ” 
  &&  “ (d0 <= 255) ” 
  &&  “ (copy_lookup_agrees a d0 xs ) ” 
  &&  “ (copy_lookup_input_safe d0 pCSpace1 (copy_counter (a) (d0)) lookup_object xs ) ” 
  &&  “ (copy_call_records h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs ) ”
  &&  (copy_lookup_resources ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 (copy_counter (a) (d0)) xs )
  **  (copy_call_rest h ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 pCSpace1 xs )
.

Definition ucos_CNode_Copy_partial_solve_wit_3 := ucos_CNode_Copy_partial_solve_wit_3_pure -> ucos_CNode_Copy_partial_solve_wit_3_aux.

Definition ucos_CNode_Copy_partial_solve_wit_4 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right"))) ,
  (copy_hole (copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2)) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> (copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ”
  &&  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_)
  **  (copy_hole (copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2)) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right") )
.

Definition ucos_CNode_Copy_partial_solve_wit_5 := 
forall (f0: Z) (s0: Z) (d0: Z) (h: (@list copy_cell)) (a: copy_state) (hc: (@list copy_cell)) (pCSpace1: Z) (pCSpace2: Z) (cap1: Z) (idx: Z) (cap2: Z) (lookup_object: Z) (PreH1 : (f0 < 255)) (PreH2 : (d0 < 64)) (PreH3 : (s0 < 64)) (PreH4 : (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 )) (PreH5 : (pCSpace1 = (copy_table (a) (d0)))) (PreH6 : (pCSpace2 = (copy_table (a) (s0)))) (PreH7 : (pCSpace1 <> 0)) (PreH8 : (pCSpace2 <> 0)) (PreH9 : (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH10 : (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))) (PreH11 : ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2)) (PreH12 : (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) (PreH13 : (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx )) (PreH14 : (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t"))) ,
  (copy_hole (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
  **  ((&((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))
|--
  “ (f0 < 255) ” 
  &&  “ (d0 < 64) ” 
  &&  “ (s0 < 64) ” 
  &&  “ (copy_pre h a ( &( "OSCSpacePrioTbl" ) ) ( &( "OSCSpaceObjectPointer" ) ) sizeof(PTR) sizeof( "slot" ) d0 s0 f0 ) ” 
  &&  “ (pCSpace1 = (copy_table (a) (d0))) ” 
  &&  “ (pCSpace2 = (copy_table (a) (s0))) ” 
  &&  “ (pCSpace1 <> 0) ” 
  &&  “ (pCSpace2 <> 0) ” 
  &&  “ (cap1 = &(((&((pCSpace1)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (idx * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ (cap2 = &(((&((pCSpace2)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (f0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability")) ” 
  &&  “ ((copy_tag ((copy_slots (a) ((copy_table (a) (s0))) (f0)))) = 2) ” 
  &&  “ (lookup_object = (copy_pointer ((copy_slots (a) ((copy_table (a) (s0))) (f0))))) ” 
  &&  “ (copy_allocation_state h hc a ( &( "OSCSpaceObjectPointer" ) ) d0 lookup_object idx ) ” 
  &&  “ (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") = &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) ”
  &&  ((&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
  **  (copy_hole (copy_put ((copy_put (hc) (&((cap1)  # "cap" ->ₛ "cap_type")) (2))) (&((cap1)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_right")) ((copy_word0 ((copy_slots (a) ((copy_table (a) (s0))) (f0)))))) &((cap2)  # "cap" ->ₛ "cap_content" .ₛ "object" .ₛ "object_t") )
.

Module Type VC_Correct.


Axiom proof_of_ucos_CNode_Copy_safety_wit_1 : ucos_CNode_Copy_safety_wit_1.
Axiom proof_of_ucos_CNode_Copy_safety_wit_2 : ucos_CNode_Copy_safety_wit_2.
Axiom proof_of_ucos_CNode_Copy_safety_wit_3 : ucos_CNode_Copy_safety_wit_3.
Axiom proof_of_ucos_CNode_Copy_safety_wit_4 : ucos_CNode_Copy_safety_wit_4.
Axiom proof_of_ucos_CNode_Copy_safety_wit_5 : ucos_CNode_Copy_safety_wit_5.
Axiom proof_of_ucos_CNode_Copy_safety_wit_6 : ucos_CNode_Copy_safety_wit_6.
Axiom proof_of_ucos_CNode_Copy_entail_wit_1 : ucos_CNode_Copy_entail_wit_1.
Axiom proof_of_ucos_CNode_Copy_entail_wit_2 : ucos_CNode_Copy_entail_wit_2.
Axiom proof_of_ucos_CNode_Copy_entail_wit_3 : ucos_CNode_Copy_entail_wit_3.
Axiom proof_of_ucos_CNode_Copy_entail_wit_4 : ucos_CNode_Copy_entail_wit_4.
Axiom proof_of_ucos_CNode_Copy_entail_wit_5 : ucos_CNode_Copy_entail_wit_5.
Axiom proof_of_ucos_CNode_Copy_entail_wit_6_1 : ucos_CNode_Copy_entail_wit_6_1.
Axiom proof_of_ucos_CNode_Copy_entail_wit_6_2 : ucos_CNode_Copy_entail_wit_6_2.
Axiom proof_of_ucos_CNode_Copy_entail_wit_7 : ucos_CNode_Copy_entail_wit_7.
Axiom proof_of_ucos_CNode_Copy_entail_wit_8 : ucos_CNode_Copy_entail_wit_8.
Axiom proof_of_ucos_CNode_Copy_entail_wit_9 : ucos_CNode_Copy_entail_wit_9.
Axiom proof_of_ucos_CNode_Copy_entail_wit_10 : ucos_CNode_Copy_entail_wit_10.
Axiom proof_of_ucos_CNode_Copy_entail_wit_11_1 : ucos_CNode_Copy_entail_wit_11_1.
Axiom proof_of_ucos_CNode_Copy_entail_wit_11_2 : ucos_CNode_Copy_entail_wit_11_2.
Axiom proof_of_ucos_CNode_Copy_entail_wit_12 : ucos_CNode_Copy_entail_wit_12.
Axiom proof_of_ucos_CNode_Copy_entail_wit_13 : ucos_CNode_Copy_entail_wit_13.
Axiom proof_of_ucos_CNode_Copy_entail_wit_14_1 : ucos_CNode_Copy_entail_wit_14_1.
Axiom proof_of_ucos_CNode_Copy_entail_wit_14_2 : ucos_CNode_Copy_entail_wit_14_2.
Axiom proof_of_ucos_CNode_Copy_return_wit_1 : ucos_CNode_Copy_return_wit_1.
Axiom proof_of_ucos_CNode_Copy_return_wit_2 : ucos_CNode_Copy_return_wit_2.
Axiom proof_of_ucos_CNode_Copy_return_wit_3 : ucos_CNode_Copy_return_wit_3.
Axiom proof_of_ucos_CNode_Copy_return_wit_4 : ucos_CNode_Copy_return_wit_4.
Axiom proof_of_ucos_CNode_Copy_return_wit_5 : ucos_CNode_Copy_return_wit_5.
Axiom proof_of_ucos_CNode_Copy_return_wit_6 : ucos_CNode_Copy_return_wit_6.
Axiom proof_of_ucos_CNode_Copy_return_wit_7 : ucos_CNode_Copy_return_wit_7.
Axiom proof_of_ucos_CNode_Copy_return_wit_8 : ucos_CNode_Copy_return_wit_8.
Axiom proof_of_ucos_CNode_Copy_return_wit_9 : ucos_CNode_Copy_return_wit_9.
Axiom proof_of_ucos_CNode_Copy_return_wit_10 : ucos_CNode_Copy_return_wit_10.
Axiom proof_of_ucos_CNode_Copy_return_wit_11 : ucos_CNode_Copy_return_wit_11.
Axiom proof_of_ucos_CNode_Copy_partial_solve_wit_1 : ucos_CNode_Copy_partial_solve_wit_1.
Axiom proof_of_ucos_CNode_Copy_partial_solve_wit_2 : ucos_CNode_Copy_partial_solve_wit_2.
Axiom proof_of_ucos_CNode_Copy_partial_solve_wit_3_pure : ucos_CNode_Copy_partial_solve_wit_3_pure.
Axiom proof_of_ucos_CNode_Copy_partial_solve_wit_3 : ucos_CNode_Copy_partial_solve_wit_3.
Axiom proof_of_ucos_CNode_Copy_partial_solve_wit_4 : ucos_CNode_Copy_partial_solve_wit_4.
Axiom proof_of_ucos_CNode_Copy_partial_solve_wit_5 : ucos_CNode_Copy_partial_solve_wit_5.

End VC_Correct.
