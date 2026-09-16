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
Require Import SimpleC.EE.osverify_qcp.cases.ucos_CNode_Delete_lib.
Local Open Scope sac.

(*----- Function ucos_CNode_Delete -----*)

Definition ucos_CNode_Delete_safety_wit_1_slot_invalid := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_slot_invalid: Z) (dest_slot_invalid: Z) (PreH1 : (func_capability_pre < 255)) (PreH2 : (destTask_Prio_pre = dest_slot_invalid)) (PreH3 : (func_capability_pre = slot_slot_invalid)) (PreH4 : (0 <= dest_slot_invalid)) (PreH5 : (dest_slot_invalid <= 255)) (PreH6 : ((unsigned_last_nbits (dest_slot_invalid) (32)) = dest_slot_invalid)) (PreH7 : (255 <= slot_slot_invalid)) (PreH8 : (slot_slot_invalid <= UINT_MAX)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_2_prio_invalid := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = dest_prio_invalid)) (PreH3 : (func_capability_pre = slot_prio_invalid)) (PreH4 : (64 <= dest_prio_invalid)) (PreH5 : (dest_prio_invalid <= 255)) (PreH6 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH7 : (0 <= slot_prio_invalid)) (PreH8 : (slot_prio_invalid < 255)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_3_null_target := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_null_target: Z) (dest_null_target: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = dest_null_target)) (PreH3 : (func_capability_pre = slot_null_target)) (PreH4 : (0 <= dest_null_target)) (PreH5 : (dest_null_target < 64)) (PreH6 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH7 : (0 <= slot_null_target)) (PreH8 : (slot_null_target < 255)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_4_unsupported_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH3 : (func_capability_pre = slot_unsupported_cap)) (PreH4 : (0 <= dest_unsupported_cap)) (PreH5 : (dest_unsupported_cap < 64)) (PreH6 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH7 : (0 <= slot_unsupported_cap)) (PreH8 : (slot_unsupported_cap < 255)) (PreH9 : (target_unsupported_cap <> 0)) (PreH10 : (old_cap_unsupported_cap <> 1)) (PreH11 : (old_cap_unsupported_cap <> 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_unsupported_cap * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_5_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = dest_category_cap)) (PreH3 : (func_capability_pre = slot_category_cap)) (PreH4 : (0 <= dest_category_cap)) (PreH5 : (dest_category_cap < 64)) (PreH6 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH7 : (0 <= slot_category_cap)) (PreH8 : (slot_category_cap < 255)) (PreH9 : (target_category_cap <> 0)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_category_cap * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_6_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = dest_object_cap)) (PreH3 : (func_capability_pre = slot_object_cap)) (PreH4 : (0 <= dest_object_cap)) (PreH5 : (dest_object_cap < 64)) (PreH6 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH7 : (0 <= slot_object_cap)) (PreH8 : (slot_object_cap < 255)) (PreH9 : (target_object_cap <> 0)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_object_cap * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 2)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_7_prio_invalid := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_prio_invalid)) (PreH4 : (func_capability_pre = slot_prio_invalid)) (PreH5 : (64 <= dest_prio_invalid)) (PreH6 : (dest_prio_invalid <= 255)) (PreH7 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH8 : (0 <= slot_prio_invalid)) (PreH9 : (slot_prio_invalid < 255)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_8_null_target := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_null_target: Z) (dest_null_target: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_null_target)) (PreH4 : (func_capability_pre = slot_null_target)) (PreH5 : (0 <= dest_null_target)) (PreH6 : (dest_null_target < 64)) (PreH7 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH8 : (0 <= slot_null_target)) (PreH9 : (slot_null_target < 255)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_9_unsupported_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH4 : (func_capability_pre = slot_unsupported_cap)) (PreH5 : (0 <= dest_unsupported_cap)) (PreH6 : (dest_unsupported_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH8 : (0 <= slot_unsupported_cap)) (PreH9 : (slot_unsupported_cap < 255)) (PreH10 : (target_unsupported_cap <> 0)) (PreH11 : (old_cap_unsupported_cap <> 1)) (PreH12 : (old_cap_unsupported_cap <> 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_unsupported_cap * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_10_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_category_cap)) (PreH4 : (func_capability_pre = slot_category_cap)) (PreH5 : (0 <= dest_category_cap)) (PreH6 : (dest_category_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH8 : (0 <= slot_category_cap)) (PreH9 : (slot_category_cap < 255)) (PreH10 : (target_category_cap <> 0)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_category_cap * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_11_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_object_cap)) (PreH4 : (func_capability_pre = slot_object_cap)) (PreH5 : (0 <= dest_object_cap)) (PreH6 : (dest_object_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH8 : (0 <= slot_object_cap)) (PreH9 : (slot_object_cap < 255)) (PreH10 : (target_object_cap <> 0)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_object_cap * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 2)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_12_null_target := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_null_target: Z) (dest_null_target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_null_target)) (PreH4 : (func_capability_pre = slot_null_target)) (PreH5 : (0 <= dest_null_target)) (PreH6 : (dest_null_target < 64)) (PreH7 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH8 : (0 <= slot_null_target)) (PreH9 : (slot_null_target < 255)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_safety_wit_13_unsupported_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH4 : (func_capability_pre = slot_unsupported_cap)) (PreH5 : (0 <= dest_unsupported_cap)) (PreH6 : (dest_unsupported_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH8 : (0 <= slot_unsupported_cap)) (PreH9 : (slot_unsupported_cap < 255)) (PreH10 : (target_unsupported_cap <> 0)) (PreH11 : (old_cap_unsupported_cap <> 1)) (PreH12 : (old_cap_unsupported_cap <> 2)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_unsupported_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_safety_wit_14_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_category_cap)) (PreH4 : (func_capability_pre = slot_category_cap)) (PreH5 : (0 <= dest_category_cap)) (PreH6 : (dest_category_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH8 : (0 <= slot_category_cap)) (PreH9 : (slot_category_cap < 255)) (PreH10 : (target_category_cap <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_category_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_safety_wit_15_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_object_cap)) (PreH4 : (func_capability_pre = slot_object_cap)) (PreH5 : (0 <= dest_object_cap)) (PreH6 : (dest_object_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH8 : (0 <= slot_object_cap)) (PreH9 : (slot_object_cap < 255)) (PreH10 : (target_object_cap <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_object_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 2)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_safety_wit_16_unsupported_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (target_unsupported_cap = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH5 : (func_capability_pre = slot_unsupported_cap)) (PreH6 : (0 <= dest_unsupported_cap)) (PreH7 : (dest_unsupported_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH9 : (0 <= slot_unsupported_cap)) (PreH10 : (slot_unsupported_cap < 255)) (PreH11 : (target_unsupported_cap <> 0)) (PreH12 : (old_cap_unsupported_cap <> 1)) (PreH13 : (old_cap_unsupported_cap <> 2)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_unsupported_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_17_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (target_category_cap = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_category_cap)) (PreH5 : (func_capability_pre = slot_category_cap)) (PreH6 : (0 <= dest_category_cap)) (PreH7 : (dest_category_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH9 : (0 <= slot_category_cap)) (PreH10 : (slot_category_cap < 255)) (PreH11 : (target_category_cap <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_category_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_18_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (target_object_cap = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_object_cap)) (PreH5 : (func_capability_pre = slot_object_cap)) (PreH6 : (0 <= dest_object_cap)) (PreH7 : (dest_object_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH9 : (0 <= slot_object_cap)) (PreH10 : (slot_object_cap < 255)) (PreH11 : (target_object_cap <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_object_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 2)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_19_unsupported_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (old_cap_unsupported_cap = 1)) (PreH2 : (target_unsupported_cap <> 0)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre < 255)) (PreH5 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH6 : (func_capability_pre = slot_unsupported_cap)) (PreH7 : (0 <= dest_unsupported_cap)) (PreH8 : (dest_unsupported_cap < 64)) (PreH9 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH10 : (0 <= slot_unsupported_cap)) (PreH11 : (slot_unsupported_cap < 255)) (PreH12 : (target_unsupported_cap <> 0)) (PreH13 : (old_cap_unsupported_cap <> 1)) (PreH14 : (old_cap_unsupported_cap <> 2)) ,
  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((( &( "cap1" ) )) # Ptr  |-> &(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_unsupported_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_20_unsupported_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (old_cap_unsupported_cap = 2)) (PreH2 : (old_cap_unsupported_cap <> 1)) (PreH3 : (target_unsupported_cap <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH7 : (func_capability_pre = slot_unsupported_cap)) (PreH8 : (0 <= dest_unsupported_cap)) (PreH9 : (dest_unsupported_cap < 64)) (PreH10 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH11 : (0 <= slot_unsupported_cap)) (PreH12 : (slot_unsupported_cap < 255)) (PreH13 : (target_unsupported_cap <> 0)) (PreH14 : (old_cap_unsupported_cap <> 1)) (PreH15 : (old_cap_unsupported_cap <> 2)) ,
  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((( &( "cap1" ) )) # Ptr  |-> &(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_unsupported_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_21_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (target_object_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_object_cap)) (PreH5 : (func_capability_pre = slot_object_cap)) (PreH6 : (0 <= dest_object_cap)) (PreH7 : (dest_object_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH9 : (0 <= slot_object_cap)) (PreH10 : (slot_object_cap < 255)) (PreH11 : (target_object_cap <> 0)) ,
  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((( &( "cap1" ) )) # Ptr  |-> &(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_object_cap)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_return_wit_1_category_cap := 
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (target_category_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_category_cap)) (PreH5 : (func_capability_pre = slot_category_cap)) (PreH6 : (0 <= dest_category_cap)) (PreH7 : (dest_category_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH9 : (0 <= slot_category_cap)) (PreH10 : (slot_category_cap < 255)) (PreH11 : (target_category_cap <> 0)) ,
  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ (0 = 0) ” 
  &&  “ (delete_slot_transition 0 old_slot_category_cap 1 word0_category_cap word1_category_cap ptr_category_cap 0 0 0 0 ptr_category_cap ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_category_cap * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
) \/
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (target_category_cap <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre = dest_category_cap)) (PreH7 : (func_capability_pre = slot_category_cap)) (PreH8 : (0 <= dest_category_cap)) (PreH9 : (dest_category_cap < 64)) (PreH10 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH11 : (0 <= slot_category_cap)) (PreH12 : (slot_category_cap < 255)) (PreH13 : (target_category_cap <> 0)) ,
  TT && emp 
|--
  “ (delete_slot_transition 0 old_slot_category_cap 1 word0_category_cap word1_category_cap ptr_category_cap 0 0 0 0 ptr_category_cap ) ”
  &&  emp
).

Definition ucos_CNode_Delete_return_wit_1_category_cap_split_goal_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (target_category_cap <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre = dest_category_cap)) (PreH7 : (func_capability_pre = slot_category_cap)) (PreH8 : (0 <= dest_category_cap)) (PreH9 : (dest_category_cap < 64)) (PreH10 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH11 : (0 <= slot_category_cap)) (PreH12 : (slot_category_cap < 255)) (PreH13 : (target_category_cap <> 0)) ,
  (delete_slot_transition 0 old_slot_category_cap 1 word0_category_cap word1_category_cap ptr_category_cap 0 0 0 0 ptr_category_cap )
.

Definition ucos_CNode_Delete_return_wit_2_object_cap := 
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (target_object_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_object_cap)) (PreH5 : (func_capability_pre = slot_object_cap)) (PreH6 : (0 <= dest_object_cap)) (PreH7 : (dest_object_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH9 : (0 <= slot_object_cap)) (PreH10 : (slot_object_cap < 255)) (PreH11 : (target_object_cap <> 0)) ,
  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
|--
  “ (0 = 0) ” 
  &&  “ (delete_slot_transition 0 old_slot_object_cap 2 word0_object_cap word1_object_cap ptr_object_cap 0 0 0 word1_object_cap 0 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_object_cap * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> 0)
) \/
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (target_object_cap <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre = dest_object_cap)) (PreH7 : (func_capability_pre = slot_object_cap)) (PreH8 : (0 <= dest_object_cap)) (PreH9 : (dest_object_cap < 64)) (PreH10 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH11 : (0 <= slot_object_cap)) (PreH12 : (slot_object_cap < 255)) (PreH13 : (target_object_cap <> 0)) ,
  TT && emp 
|--
  “ (delete_slot_transition 0 old_slot_object_cap 2 word0_object_cap word1_object_cap ptr_object_cap 0 0 0 word1_object_cap 0 ) ”
  &&  emp
).

Definition ucos_CNode_Delete_return_wit_2_object_cap_split_goal_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (target_object_cap <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre = dest_object_cap)) (PreH7 : (func_capability_pre = slot_object_cap)) (PreH8 : (0 <= dest_object_cap)) (PreH9 : (dest_object_cap < 64)) (PreH10 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH11 : (0 <= slot_object_cap)) (PreH12 : (slot_object_cap < 255)) (PreH13 : (target_object_cap <> 0)) ,
  (delete_slot_transition 0 old_slot_object_cap 2 word0_object_cap word1_object_cap ptr_object_cap 0 0 0 word1_object_cap 0 )
.

Definition ucos_CNode_Delete_return_wit_3_unsupported_cap := 
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (old_cap_unsupported_cap <> 2)) (PreH2 : (old_cap_unsupported_cap <> 1)) (PreH3 : (target_unsupported_cap <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH7 : (func_capability_pre = slot_unsupported_cap)) (PreH8 : (0 <= dest_unsupported_cap)) (PreH9 : (dest_unsupported_cap < 64)) (PreH10 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH11 : (0 <= slot_unsupported_cap)) (PreH12 : (slot_unsupported_cap < 255)) (PreH13 : (target_unsupported_cap <> 0)) (PreH14 : (old_cap_unsupported_cap <> 1)) (PreH15 : (old_cap_unsupported_cap <> 2)) ,
  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ (9 = 9) ” 
  &&  “ (delete_slot_transition 9 old_slot_unsupported_cap old_cap_unsupported_cap word0_unsupported_cap word1_unsupported_cap ptr_unsupported_cap old_slot_unsupported_cap old_cap_unsupported_cap word0_unsupported_cap word1_unsupported_cap ptr_unsupported_cap ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_unsupported_cap * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
) \/
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (old_cap_unsupported_cap <= UINT_MAX)) (PreH2 : (old_cap_unsupported_cap >= 0)) (PreH3 : (old_cap_unsupported_cap <> 2)) (PreH4 : (old_cap_unsupported_cap <> 1)) (PreH5 : (target_unsupported_cap <> 0)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH9 : (func_capability_pre = slot_unsupported_cap)) (PreH10 : (0 <= dest_unsupported_cap)) (PreH11 : (dest_unsupported_cap < 64)) (PreH12 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH13 : (0 <= slot_unsupported_cap)) (PreH14 : (slot_unsupported_cap < 255)) (PreH15 : (target_unsupported_cap <> 0)) (PreH16 : (old_cap_unsupported_cap <> 1)) (PreH17 : (old_cap_unsupported_cap <> 2)) ,
  TT && emp 
|--
  “ (delete_slot_transition 9 old_slot_unsupported_cap old_cap_unsupported_cap word0_unsupported_cap word1_unsupported_cap ptr_unsupported_cap old_slot_unsupported_cap old_cap_unsupported_cap word0_unsupported_cap word1_unsupported_cap ptr_unsupported_cap ) ”
  &&  emp
).

Definition ucos_CNode_Delete_return_wit_3_unsupported_cap_split_goal_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (old_cap_unsupported_cap <= UINT_MAX)) (PreH2 : (old_cap_unsupported_cap >= 0)) (PreH3 : (old_cap_unsupported_cap <> 2)) (PreH4 : (old_cap_unsupported_cap <> 1)) (PreH5 : (target_unsupported_cap <> 0)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH9 : (func_capability_pre = slot_unsupported_cap)) (PreH10 : (0 <= dest_unsupported_cap)) (PreH11 : (dest_unsupported_cap < 64)) (PreH12 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH13 : (0 <= slot_unsupported_cap)) (PreH14 : (slot_unsupported_cap < 255)) (PreH15 : (target_unsupported_cap <> 0)) (PreH16 : (old_cap_unsupported_cap <> 1)) (PreH17 : (old_cap_unsupported_cap <> 2)) ,
  (delete_slot_transition 9 old_slot_unsupported_cap old_cap_unsupported_cap word0_unsupported_cap word1_unsupported_cap ptr_unsupported_cap old_slot_unsupported_cap old_cap_unsupported_cap word0_unsupported_cap word1_unsupported_cap ptr_unsupported_cap )
.

Definition ucos_CNode_Delete_return_wit_4_null_target := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_null_target: Z) (dest_null_target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_null_target)) (PreH4 : (func_capability_pre = slot_null_target)) (PreH5 : (0 <= dest_null_target)) (PreH6 : (dest_null_target < 64)) (PreH7 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH8 : (0 <= slot_null_target)) (PreH9 : (slot_null_target < 255)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ (9 = 9) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_CNode_Delete_return_wit_5_prio_invalid := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_prio_invalid)) (PreH4 : (func_capability_pre = slot_prio_invalid)) (PreH5 : (64 <= dest_prio_invalid)) (PreH6 : (dest_prio_invalid <= 255)) (PreH7 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH8 : (0 <= slot_prio_invalid)) (PreH9 : (slot_prio_invalid < 255)) ,
  TT && emp 
|--
  “ (9 = 9) ”
  &&  emp
.

Definition ucos_CNode_Delete_return_wit_6_slot_invalid := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_slot_invalid: Z) (dest_slot_invalid: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (destTask_Prio_pre = dest_slot_invalid)) (PreH3 : (func_capability_pre = slot_slot_invalid)) (PreH4 : (0 <= dest_slot_invalid)) (PreH5 : (dest_slot_invalid <= 255)) (PreH6 : ((unsigned_last_nbits (dest_slot_invalid) (32)) = dest_slot_invalid)) (PreH7 : (255 <= slot_slot_invalid)) (PreH8 : (slot_slot_invalid <= UINT_MAX)) ,
  TT && emp 
|--
  “ (9 = 9) ”
  &&  emp
.

Definition ucos_CNode_Delete_partial_solve_wit_1_null_target := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (slot_null_target: Z) (dest_null_target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_null_target)) (PreH4 : (func_capability_pre = slot_null_target)) (PreH5 : (0 <= dest_null_target)) (PreH6 : (dest_null_target < 64)) (PreH7 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH8 : (0 <= slot_null_target)) (PreH9 : (slot_null_target < 255)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_null_target) ” 
  &&  “ (func_capability_pre = slot_null_target) ” 
  &&  “ (0 <= dest_null_target) ” 
  &&  “ (dest_null_target < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target) ” 
  &&  “ (0 <= slot_null_target) ” 
  &&  “ (slot_null_target < 255) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_CNode_Delete_partial_solve_wit_2_unsupported_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH4 : (func_capability_pre = slot_unsupported_cap)) (PreH5 : (0 <= dest_unsupported_cap)) (PreH6 : (dest_unsupported_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH8 : (0 <= slot_unsupported_cap)) (PreH9 : (slot_unsupported_cap < 255)) (PreH10 : (target_unsupported_cap <> 0)) (PreH11 : (old_cap_unsupported_cap <> 1)) (PreH12 : (old_cap_unsupported_cap <> 2)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_unsupported_cap * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_unsupported_cap) ” 
  &&  “ (func_capability_pre = slot_unsupported_cap) ” 
  &&  “ (0 <= dest_unsupported_cap) ” 
  &&  “ (dest_unsupported_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap) ” 
  &&  “ (0 <= slot_unsupported_cap) ” 
  &&  “ (slot_unsupported_cap < 255) ” 
  &&  “ (target_unsupported_cap <> 0) ” 
  &&  “ (old_cap_unsupported_cap <> 1) ” 
  &&  “ (old_cap_unsupported_cap <> 2) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_3_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_category_cap)) (PreH4 : (func_capability_pre = slot_category_cap)) (PreH5 : (0 <= dest_category_cap)) (PreH6 : (dest_category_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH8 : (0 <= slot_category_cap)) (PreH9 : (slot_category_cap < 255)) (PreH10 : (target_category_cap <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_category_cap * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_category_cap) ” 
  &&  “ (func_capability_pre = slot_category_cap) ” 
  &&  “ (0 <= dest_category_cap) ” 
  &&  “ (dest_category_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap) ” 
  &&  “ (0 <= slot_category_cap) ” 
  &&  “ (slot_category_cap < 255) ” 
  &&  “ (target_category_cap <> 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_4_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (destTask_Prio_pre = dest_object_cap)) (PreH4 : (func_capability_pre = slot_object_cap)) (PreH5 : (0 <= dest_object_cap)) (PreH6 : (dest_object_cap < 64)) (PreH7 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH8 : (0 <= slot_object_cap)) (PreH9 : (slot_object_cap < 255)) (PreH10 : (target_object_cap <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_object_cap * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 2)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_object_cap) ” 
  &&  “ (func_capability_pre = slot_object_cap) ” 
  &&  “ (0 <= dest_object_cap) ” 
  &&  “ (dest_object_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap) ” 
  &&  “ (0 <= slot_object_cap) ” 
  &&  “ (slot_object_cap < 255) ” 
  &&  “ (target_object_cap <> 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 2)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_5_unsupported_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_unsupported_cap: Z) (word1_unsupported_cap: Z) (word0_unsupported_cap: Z) (old_cap_unsupported_cap: Z) (old_slot_unsupported_cap: Z) (target_unsupported_cap: Z) (slot_unsupported_cap: Z) (dest_unsupported_cap: Z) (PreH1 : (target_unsupported_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_unsupported_cap)) (PreH5 : (func_capability_pre = slot_unsupported_cap)) (PreH6 : (0 <= dest_unsupported_cap)) (PreH7 : (dest_unsupported_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap)) (PreH9 : (0 <= slot_unsupported_cap)) (PreH10 : (slot_unsupported_cap < 255)) (PreH11 : (target_unsupported_cap <> 0)) (PreH12 : (old_cap_unsupported_cap <> 1)) (PreH13 : (old_cap_unsupported_cap <> 2)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
|--
  “ (target_unsupported_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_unsupported_cap) ” 
  &&  “ (func_capability_pre = slot_unsupported_cap) ” 
  &&  “ (0 <= dest_unsupported_cap) ” 
  &&  “ (dest_unsupported_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_unsupported_cap) (32)) = dest_unsupported_cap) ” 
  &&  “ (0 <= slot_unsupported_cap) ” 
  &&  “ (slot_unsupported_cap < 255) ” 
  &&  “ (target_unsupported_cap <> 0) ” 
  &&  “ (old_cap_unsupported_cap <> 1) ” 
  &&  “ (old_cap_unsupported_cap <> 2) ”
  &&  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_cap_unsupported_cap)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_unsupported_cap)
  **  ((&(((&((target_unsupported_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_unsupported_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_unsupported_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_6_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (target_category_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_category_cap)) (PreH5 : (func_capability_pre = slot_category_cap)) (PreH6 : (0 <= dest_category_cap)) (PreH7 : (dest_category_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH9 : (0 <= slot_category_cap)) (PreH10 : (slot_category_cap < 255)) (PreH11 : (target_category_cap <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ (target_category_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_category_cap) ” 
  &&  “ (func_capability_pre = slot_category_cap) ” 
  &&  “ (0 <= dest_category_cap) ” 
  &&  “ (dest_category_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap) ” 
  &&  “ (0 <= slot_category_cap) ” 
  &&  “ (slot_category_cap < 255) ” 
  &&  “ (target_category_cap <> 0) ”
  &&  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_7_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (target_object_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_object_cap)) (PreH5 : (func_capability_pre = slot_object_cap)) (PreH6 : (0 <= dest_object_cap)) (PreH7 : (dest_object_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH9 : (0 <= slot_object_cap)) (PreH10 : (slot_object_cap < 255)) (PreH11 : (target_object_cap <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 2)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ (target_object_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_object_cap) ” 
  &&  “ (func_capability_pre = slot_object_cap) ” 
  &&  “ (0 <= dest_object_cap) ” 
  &&  “ (dest_object_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap) ” 
  &&  “ (0 <= slot_object_cap) ” 
  &&  “ (slot_object_cap < 255) ” 
  &&  “ (target_object_cap <> 0) ”
  &&  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 2)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_8_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (word0_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (target_category_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_category_cap)) (PreH5 : (func_capability_pre = slot_category_cap)) (PreH6 : (0 <= dest_category_cap)) (PreH7 : (dest_category_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH9 : (0 <= slot_category_cap)) (PreH10 : (slot_category_cap < 255)) (PreH11 : (target_category_cap <> 0)) ,
  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ (target_category_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_category_cap) ” 
  &&  “ (func_capability_pre = slot_category_cap) ” 
  &&  “ (0 <= dest_category_cap) ” 
  &&  “ (dest_category_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap) ” 
  &&  “ (0 <= slot_category_cap) ” 
  &&  “ (slot_category_cap < 255) ” 
  &&  “ (target_category_cap <> 0) ”
  &&  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_9_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (word1_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (target_category_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_category_cap)) (PreH5 : (func_capability_pre = slot_category_cap)) (PreH6 : (0 <= dest_category_cap)) (PreH7 : (dest_category_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH9 : (0 <= slot_category_cap)) (PreH10 : (slot_category_cap < 255)) (PreH11 : (target_category_cap <> 0)) ,
  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ (target_category_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_category_cap) ” 
  &&  “ (func_capability_pre = slot_category_cap) ” 
  &&  “ (0 <= dest_category_cap) ” 
  &&  “ (dest_category_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap) ” 
  &&  “ (0 <= slot_category_cap) ” 
  &&  “ (slot_category_cap < 255) ” 
  &&  “ (target_category_cap <> 0) ”
  &&  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_10_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (word0_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (target_object_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_object_cap)) (PreH5 : (func_capability_pre = slot_object_cap)) (PreH6 : (0 <= dest_object_cap)) (PreH7 : (dest_object_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH9 : (0 <= slot_object_cap)) (PreH10 : (slot_object_cap < 255)) (PreH11 : (target_object_cap <> 0)) ,
  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> word0_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ (target_object_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_object_cap) ” 
  &&  “ (func_capability_pre = slot_object_cap) ” 
  &&  “ (0 <= dest_object_cap) ” 
  &&  “ (dest_object_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap) ” 
  &&  “ (0 <= slot_object_cap) ” 
  &&  “ (slot_object_cap < 255) ” 
  &&  “ (target_object_cap <> 0) ”
  &&  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_11_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_object_cap: Z) (word1_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (target_object_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_object_cap)) (PreH5 : (func_capability_pre = slot_object_cap)) (PreH6 : (0 <= dest_object_cap)) (PreH7 : (dest_object_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH9 : (0 <= slot_object_cap)) (PreH10 : (slot_object_cap < 255)) (PreH11 : (target_object_cap <> 0)) ,
  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> ptr_object_cap)
|--
  “ (target_object_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_object_cap) ” 
  &&  “ (func_capability_pre = slot_object_cap) ” 
  &&  “ (0 <= dest_object_cap) ” 
  &&  “ (dest_object_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap) ” 
  &&  “ (0 <= slot_object_cap) ” 
  &&  “ (slot_object_cap < 255) ” 
  &&  “ (target_object_cap <> 0) ”
  &&  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_12_category_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (ptr_category_cap: Z) (old_slot_category_cap: Z) (target_category_cap: Z) (slot_category_cap: Z) (dest_category_cap: Z) (PreH1 : (target_category_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_category_cap)) (PreH5 : (func_capability_pre = slot_category_cap)) (PreH6 : (0 <= dest_category_cap)) (PreH7 : (dest_category_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap)) (PreH9 : (0 <= slot_category_cap)) (PreH10 : (slot_category_cap < 255)) (PreH11 : (target_category_cap <> 0)) ,
  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
|--
  “ (target_category_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_category_cap) ” 
  &&  “ (func_capability_pre = slot_category_cap) ” 
  &&  “ (0 <= dest_category_cap) ” 
  &&  “ (dest_category_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_category_cap) (32)) = dest_category_cap) ” 
  &&  “ (0 <= slot_category_cap) ” 
  &&  “ (slot_category_cap < 255) ” 
  &&  “ (target_category_cap <> 0) ”
  &&  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> 0)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_category_cap)
  **  ((&(((&((target_category_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_category_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "Dummy_ptr")) # Ptr  |-> ptr_category_cap)
.

Definition ucos_CNode_Delete_partial_solve_wit_13_object_cap := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (word1_object_cap: Z) (old_slot_object_cap: Z) (target_object_cap: Z) (slot_object_cap: Z) (dest_object_cap: Z) (PreH1 : (target_object_cap <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (destTask_Prio_pre = dest_object_cap)) (PreH5 : (func_capability_pre = slot_object_cap)) (PreH6 : (0 <= dest_object_cap)) (PreH7 : (dest_object_cap < 64)) (PreH8 : ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap)) (PreH9 : (0 <= slot_object_cap)) (PreH10 : (slot_object_cap < 255)) (PreH11 : (target_object_cap <> 0)) ,
  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> old_slot_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
|--
  “ (target_object_cap <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre = dest_object_cap) ” 
  &&  “ (func_capability_pre = slot_object_cap) ” 
  &&  “ (0 <= dest_object_cap) ” 
  &&  “ (dest_object_cap < 64) ” 
  &&  “ ((unsigned_last_nbits (dest_object_cap) (32)) = dest_object_cap) ” 
  &&  “ (0 <= slot_object_cap) ” 
  &&  “ (slot_object_cap < 255) ” 
  &&  “ (target_object_cap <> 0) ”
  &&  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_object_cap)
  **  ((&(((&((target_object_cap)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_object_cap * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "Dummy_int")) # UInt  |-> word1_object_cap)
.

Module Type VC_Correct.


Axiom proof_of_ucos_CNode_Delete_safety_wit_1_slot_invalid : ucos_CNode_Delete_safety_wit_1_slot_invalid.
Axiom proof_of_ucos_CNode_Delete_safety_wit_2_prio_invalid : ucos_CNode_Delete_safety_wit_2_prio_invalid.
Axiom proof_of_ucos_CNode_Delete_safety_wit_3_null_target : ucos_CNode_Delete_safety_wit_3_null_target.
Axiom proof_of_ucos_CNode_Delete_safety_wit_4_unsupported_cap : ucos_CNode_Delete_safety_wit_4_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_5_category_cap : ucos_CNode_Delete_safety_wit_5_category_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_6_object_cap : ucos_CNode_Delete_safety_wit_6_object_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_7_prio_invalid : ucos_CNode_Delete_safety_wit_7_prio_invalid.
Axiom proof_of_ucos_CNode_Delete_safety_wit_8_null_target : ucos_CNode_Delete_safety_wit_8_null_target.
Axiom proof_of_ucos_CNode_Delete_safety_wit_9_unsupported_cap : ucos_CNode_Delete_safety_wit_9_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_10_category_cap : ucos_CNode_Delete_safety_wit_10_category_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_11_object_cap : ucos_CNode_Delete_safety_wit_11_object_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_12_null_target : ucos_CNode_Delete_safety_wit_12_null_target.
Axiom proof_of_ucos_CNode_Delete_safety_wit_13_unsupported_cap : ucos_CNode_Delete_safety_wit_13_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_14_category_cap : ucos_CNode_Delete_safety_wit_14_category_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_15_object_cap : ucos_CNode_Delete_safety_wit_15_object_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_16_unsupported_cap : ucos_CNode_Delete_safety_wit_16_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_17_category_cap : ucos_CNode_Delete_safety_wit_17_category_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_18_object_cap : ucos_CNode_Delete_safety_wit_18_object_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_19_unsupported_cap : ucos_CNode_Delete_safety_wit_19_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_20_unsupported_cap : ucos_CNode_Delete_safety_wit_20_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_safety_wit_21_object_cap : ucos_CNode_Delete_safety_wit_21_object_cap.
Axiom proof_of_ucos_CNode_Delete_return_wit_1_category_cap : ucos_CNode_Delete_return_wit_1_category_cap.
Axiom proof_of_ucos_CNode_Delete_return_wit_2_object_cap : ucos_CNode_Delete_return_wit_2_object_cap.
Axiom proof_of_ucos_CNode_Delete_return_wit_3_unsupported_cap : ucos_CNode_Delete_return_wit_3_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_return_wit_4_null_target : ucos_CNode_Delete_return_wit_4_null_target.
Axiom proof_of_ucos_CNode_Delete_return_wit_5_prio_invalid : ucos_CNode_Delete_return_wit_5_prio_invalid.
Axiom proof_of_ucos_CNode_Delete_return_wit_6_slot_invalid : ucos_CNode_Delete_return_wit_6_slot_invalid.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_1_null_target : ucos_CNode_Delete_partial_solve_wit_1_null_target.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_2_unsupported_cap : ucos_CNode_Delete_partial_solve_wit_2_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_3_category_cap : ucos_CNode_Delete_partial_solve_wit_3_category_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_4_object_cap : ucos_CNode_Delete_partial_solve_wit_4_object_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_5_unsupported_cap : ucos_CNode_Delete_partial_solve_wit_5_unsupported_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_6_category_cap : ucos_CNode_Delete_partial_solve_wit_6_category_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_7_object_cap : ucos_CNode_Delete_partial_solve_wit_7_object_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_8_category_cap : ucos_CNode_Delete_partial_solve_wit_8_category_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_9_category_cap : ucos_CNode_Delete_partial_solve_wit_9_category_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_10_object_cap : ucos_CNode_Delete_partial_solve_wit_10_object_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_11_object_cap : ucos_CNode_Delete_partial_solve_wit_11_object_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_12_category_cap : ucos_CNode_Delete_partial_solve_wit_12_category_cap.
Axiom proof_of_ucos_CNode_Delete_partial_solve_wit_13_object_cap : ucos_CNode_Delete_partial_solve_wit_13_object_cap.

End VC_Correct.
