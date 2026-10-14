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
Require Import SimpleC.EE.osverify_qcp.cases.ucos_CNode_Mint_lib.
Local Open Scope sac.

(*----- Function ucos_CNode_Mint -----*)

Definition ucos_CNode_Mint_safety_wit_1_class_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_class_invalid: Z) (slot_class_invalid: Z) (src_class_invalid: Z) (dest_class_invalid: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = dest_class_invalid)) (PreH3 : (srcTask_Prio_pre = src_class_invalid)) (PreH4 : (func_capability_pre = slot_class_invalid)) (PreH5 : (rights_pre = requested_class_invalid)) (PreH6 : (0 <= dest_class_invalid)) (PreH7 : (dest_class_invalid <= 255)) (PreH8 : (0 <= src_class_invalid)) (PreH9 : (src_class_invalid <= 255)) (PreH10 : ((unsigned_last_nbits (dest_class_invalid) (32)) = dest_class_invalid)) (PreH11 : ((unsigned_last_nbits (src_class_invalid) (32)) = src_class_invalid)) (PreH12 : (16 < slot_class_invalid)) (PreH13 : (slot_class_invalid <= UINT_MAX)) (PreH14 : (0 <= requested_class_invalid)) (PreH15 : (requested_class_invalid <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_2_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = dest_prio_invalid)) (PreH3 : (srcTask_Prio_pre = src_prio_invalid)) (PreH4 : (func_capability_pre = slot_prio_invalid)) (PreH5 : (rights_pre = requested_prio_invalid)) (PreH6 : (0 <= dest_prio_invalid)) (PreH7 : (dest_prio_invalid <= 255)) (PreH8 : (0 <= src_prio_invalid)) (PreH9 : (src_prio_invalid <= 255)) (PreH10 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH11 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH12 : (64 <= dest_prio_invalid)) (PreH13 : (0 <= slot_prio_invalid)) (PreH14 : (slot_prio_invalid <= 16)) (PreH15 : (0 <= requested_prio_invalid)) (PreH16 : (requested_prio_invalid <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_3_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = dest_prio_invalid)) (PreH3 : (srcTask_Prio_pre = src_prio_invalid)) (PreH4 : (func_capability_pre = slot_prio_invalid)) (PreH5 : (rights_pre = requested_prio_invalid)) (PreH6 : (0 <= dest_prio_invalid)) (PreH7 : (dest_prio_invalid <= 255)) (PreH8 : (0 <= src_prio_invalid)) (PreH9 : (src_prio_invalid <= 255)) (PreH10 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH11 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH12 : (64 <= src_prio_invalid)) (PreH13 : (0 <= slot_prio_invalid)) (PreH14 : (slot_prio_invalid <= 16)) (PreH15 : (0 <= requested_prio_invalid)) (PreH16 : (requested_prio_invalid <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_4_null_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_null_same_priority: Z) (slot_null_same_priority: Z) (prio_null_same_priority: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = prio_null_same_priority)) (PreH3 : (srcTask_Prio_pre = prio_null_same_priority)) (PreH4 : (func_capability_pre = slot_null_same_priority)) (PreH5 : (rights_pre = requested_null_same_priority)) (PreH6 : (0 <= prio_null_same_priority)) (PreH7 : (prio_null_same_priority < 64)) (PreH8 : ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority)) (PreH9 : (0 <= slot_null_same_priority)) (PreH10 : (slot_null_same_priority <= 16)) (PreH11 : (0 <= requested_null_same_priority)) (PreH12 : (requested_null_same_priority <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_null_same_priority * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_5_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH3 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH4 : (func_capability_pre = slot_null_distinct_priorities)) (PreH5 : (rights_pre = requested_null_distinct_priorities)) (PreH6 : (0 <= dest_null_distinct_priorities)) (PreH7 : (dest_null_distinct_priorities < 64)) (PreH8 : (0 <= src_null_distinct_priorities)) (PreH9 : (src_null_distinct_priorities < 64)) (PreH10 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH11 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH12 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH13 : (0 <= slot_null_distinct_priorities)) (PreH14 : (slot_null_distinct_priorities <= 16)) (PreH15 : (0 <= requested_null_distinct_priorities)) (PreH16 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH17 : (target_null_distinct_priorities = 0)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_6_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH3 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH4 : (func_capability_pre = slot_null_distinct_priorities)) (PreH5 : (rights_pre = requested_null_distinct_priorities)) (PreH6 : (0 <= dest_null_distinct_priorities)) (PreH7 : (dest_null_distinct_priorities < 64)) (PreH8 : (0 <= src_null_distinct_priorities)) (PreH9 : (src_null_distinct_priorities < 64)) (PreH10 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH11 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH12 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH13 : (0 <= slot_null_distinct_priorities)) (PreH14 : (slot_null_distinct_priorities <= 16)) (PreH15 : (0 <= requested_null_distinct_priorities)) (PreH16 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH17 : (source_null_distinct_priorities = 0)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_7_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = prio_same_priority)) (PreH3 : (srcTask_Prio_pre = prio_same_priority)) (PreH4 : (func_capability_pre = slot_same_priority)) (PreH5 : (rights_pre = requested_same_priority)) (PreH6 : (0 <= prio_same_priority)) (PreH7 : (prio_same_priority < 64)) (PreH8 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH9 : (0 <= slot_same_priority)) (PreH10 : (slot_same_priority <= 16)) (PreH11 : (target_same_priority <> 0)) (PreH12 : (0 <= requested_same_priority)) (PreH13 : (requested_same_priority <= UINT_MAX)) (PreH14 : (0 <= word1_same_priority)) (PreH15 : (word1_same_priority <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_8_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = dest_shared_cspace)) (PreH3 : (srcTask_Prio_pre = src_shared_cspace)) (PreH4 : (func_capability_pre = slot_shared_cspace)) (PreH5 : (rights_pre = requested_shared_cspace)) (PreH6 : (0 <= dest_shared_cspace)) (PreH7 : (dest_shared_cspace < 64)) (PreH8 : (0 <= src_shared_cspace)) (PreH9 : (src_shared_cspace < 64)) (PreH10 : (dest_shared_cspace <> src_shared_cspace)) (PreH11 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH12 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH13 : (0 <= slot_shared_cspace)) (PreH14 : (slot_shared_cspace <= 16)) (PreH15 : (target_shared_cspace <> 0)) (PreH16 : (0 <= requested_shared_cspace)) (PreH17 : (requested_shared_cspace <= UINT_MAX)) (PreH18 : (0 <= word1_shared_cspace)) (PreH19 : (word1_shared_cspace <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_9_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (0 > func_capability_pre)) (PreH2 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH3 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH4 : (func_capability_pre = slot_distinct_cspaces)) (PreH5 : (rights_pre = requested_distinct_cspaces)) (PreH6 : (0 <= dest_distinct_cspaces)) (PreH7 : (dest_distinct_cspaces < 64)) (PreH8 : (0 <= src_distinct_cspaces)) (PreH9 : (src_distinct_cspaces < 64)) (PreH10 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH11 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH12 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH13 : (0 <= slot_distinct_cspaces)) (PreH14 : (slot_distinct_cspaces <= 16)) (PreH15 : (target_distinct_cspaces <> 0)) (PreH16 : (source_distinct_cspaces <> 0)) (PreH17 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH18 : (0 <= requested_distinct_cspaces)) (PreH19 : (requested_distinct_cspaces <= UINT_MAX)) (PreH20 : (0 <= src_word1_distinct_cspaces)) (PreH21 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_10_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH4 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH5 : (func_capability_pre = slot_distinct_cspaces)) (PreH6 : (rights_pre = requested_distinct_cspaces)) (PreH7 : (0 <= dest_distinct_cspaces)) (PreH8 : (dest_distinct_cspaces < 64)) (PreH9 : (0 <= src_distinct_cspaces)) (PreH10 : (src_distinct_cspaces < 64)) (PreH11 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH12 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH13 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH14 : (0 <= slot_distinct_cspaces)) (PreH15 : (slot_distinct_cspaces <= 16)) (PreH16 : (target_distinct_cspaces <> 0)) (PreH17 : (source_distinct_cspaces <> 0)) (PreH18 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH19 : (0 <= requested_distinct_cspaces)) (PreH20 : (requested_distinct_cspaces <= UINT_MAX)) (PreH21 : (0 <= src_word1_distinct_cspaces)) (PreH22 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_11_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = dest_shared_cspace)) (PreH4 : (srcTask_Prio_pre = src_shared_cspace)) (PreH5 : (func_capability_pre = slot_shared_cspace)) (PreH6 : (rights_pre = requested_shared_cspace)) (PreH7 : (0 <= dest_shared_cspace)) (PreH8 : (dest_shared_cspace < 64)) (PreH9 : (0 <= src_shared_cspace)) (PreH10 : (src_shared_cspace < 64)) (PreH11 : (dest_shared_cspace <> src_shared_cspace)) (PreH12 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH13 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH14 : (0 <= slot_shared_cspace)) (PreH15 : (slot_shared_cspace <= 16)) (PreH16 : (target_shared_cspace <> 0)) (PreH17 : (0 <= requested_shared_cspace)) (PreH18 : (requested_shared_cspace <= UINT_MAX)) (PreH19 : (0 <= word1_shared_cspace)) (PreH20 : (word1_shared_cspace <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_12_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = prio_same_priority)) (PreH4 : (srcTask_Prio_pre = prio_same_priority)) (PreH5 : (func_capability_pre = slot_same_priority)) (PreH6 : (rights_pre = requested_same_priority)) (PreH7 : (0 <= prio_same_priority)) (PreH8 : (prio_same_priority < 64)) (PreH9 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH10 : (0 <= slot_same_priority)) (PreH11 : (slot_same_priority <= 16)) (PreH12 : (target_same_priority <> 0)) (PreH13 : (0 <= requested_same_priority)) (PreH14 : (requested_same_priority <= UINT_MAX)) (PreH15 : (0 <= word1_same_priority)) (PreH16 : (word1_same_priority <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_13_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH4 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH5 : (func_capability_pre = slot_null_distinct_priorities)) (PreH6 : (rights_pre = requested_null_distinct_priorities)) (PreH7 : (0 <= dest_null_distinct_priorities)) (PreH8 : (dest_null_distinct_priorities < 64)) (PreH9 : (0 <= src_null_distinct_priorities)) (PreH10 : (src_null_distinct_priorities < 64)) (PreH11 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH12 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH13 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH14 : (0 <= slot_null_distinct_priorities)) (PreH15 : (slot_null_distinct_priorities <= 16)) (PreH16 : (0 <= requested_null_distinct_priorities)) (PreH17 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH18 : (source_null_distinct_priorities = 0)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_14_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH4 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH5 : (func_capability_pre = slot_null_distinct_priorities)) (PreH6 : (rights_pre = requested_null_distinct_priorities)) (PreH7 : (0 <= dest_null_distinct_priorities)) (PreH8 : (dest_null_distinct_priorities < 64)) (PreH9 : (0 <= src_null_distinct_priorities)) (PreH10 : (src_null_distinct_priorities < 64)) (PreH11 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH12 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH13 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH14 : (0 <= slot_null_distinct_priorities)) (PreH15 : (slot_null_distinct_priorities <= 16)) (PreH16 : (0 <= requested_null_distinct_priorities)) (PreH17 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH18 : (target_null_distinct_priorities = 0)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_15_null_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_null_same_priority: Z) (slot_null_same_priority: Z) (prio_null_same_priority: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = prio_null_same_priority)) (PreH4 : (srcTask_Prio_pre = prio_null_same_priority)) (PreH5 : (func_capability_pre = slot_null_same_priority)) (PreH6 : (rights_pre = requested_null_same_priority)) (PreH7 : (0 <= prio_null_same_priority)) (PreH8 : (prio_null_same_priority < 64)) (PreH9 : ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority)) (PreH10 : (0 <= slot_null_same_priority)) (PreH11 : (slot_null_same_priority <= 16)) (PreH12 : (0 <= requested_null_same_priority)) (PreH13 : (requested_null_same_priority <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_null_same_priority * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_16_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = dest_prio_invalid)) (PreH4 : (srcTask_Prio_pre = src_prio_invalid)) (PreH5 : (func_capability_pre = slot_prio_invalid)) (PreH6 : (rights_pre = requested_prio_invalid)) (PreH7 : (0 <= dest_prio_invalid)) (PreH8 : (dest_prio_invalid <= 255)) (PreH9 : (0 <= src_prio_invalid)) (PreH10 : (src_prio_invalid <= 255)) (PreH11 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH12 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH13 : (64 <= src_prio_invalid)) (PreH14 : (0 <= slot_prio_invalid)) (PreH15 : (slot_prio_invalid <= 16)) (PreH16 : (0 <= requested_prio_invalid)) (PreH17 : (requested_prio_invalid <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_17_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = dest_prio_invalid)) (PreH4 : (srcTask_Prio_pre = src_prio_invalid)) (PreH5 : (func_capability_pre = slot_prio_invalid)) (PreH6 : (rights_pre = requested_prio_invalid)) (PreH7 : (0 <= dest_prio_invalid)) (PreH8 : (dest_prio_invalid <= 255)) (PreH9 : (0 <= src_prio_invalid)) (PreH10 : (src_prio_invalid <= 255)) (PreH11 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH12 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH13 : (64 <= dest_prio_invalid)) (PreH14 : (0 <= slot_prio_invalid)) (PreH15 : (slot_prio_invalid <= 16)) (PreH16 : (0 <= requested_prio_invalid)) (PreH17 : (requested_prio_invalid <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_18_class_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_class_invalid: Z) (slot_class_invalid: Z) (src_class_invalid: Z) (dest_class_invalid: Z) (PreH1 : (func_capability_pre <= 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = dest_class_invalid)) (PreH4 : (srcTask_Prio_pre = src_class_invalid)) (PreH5 : (func_capability_pre = slot_class_invalid)) (PreH6 : (rights_pre = requested_class_invalid)) (PreH7 : (0 <= dest_class_invalid)) (PreH8 : (dest_class_invalid <= 255)) (PreH9 : (0 <= src_class_invalid)) (PreH10 : (src_class_invalid <= 255)) (PreH11 : ((unsigned_last_nbits (dest_class_invalid) (32)) = dest_class_invalid)) (PreH12 : ((unsigned_last_nbits (src_class_invalid) (32)) = src_class_invalid)) (PreH13 : (16 < slot_class_invalid)) (PreH14 : (slot_class_invalid <= UINT_MAX)) (PreH15 : (0 <= requested_class_invalid)) (PreH16 : (requested_class_invalid <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_19_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = dest_prio_invalid)) (PreH5 : (srcTask_Prio_pre = src_prio_invalid)) (PreH6 : (func_capability_pre = slot_prio_invalid)) (PreH7 : (rights_pre = requested_prio_invalid)) (PreH8 : (0 <= dest_prio_invalid)) (PreH9 : (dest_prio_invalid <= 255)) (PreH10 : (0 <= src_prio_invalid)) (PreH11 : (src_prio_invalid <= 255)) (PreH12 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH13 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH14 : (64 <= dest_prio_invalid)) (PreH15 : (0 <= slot_prio_invalid)) (PreH16 : (slot_prio_invalid <= 16)) (PreH17 : (0 <= requested_prio_invalid)) (PreH18 : (requested_prio_invalid <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_20_null_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_null_same_priority: Z) (slot_null_same_priority: Z) (prio_null_same_priority: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = prio_null_same_priority)) (PreH5 : (srcTask_Prio_pre = prio_null_same_priority)) (PreH6 : (func_capability_pre = slot_null_same_priority)) (PreH7 : (rights_pre = requested_null_same_priority)) (PreH8 : (0 <= prio_null_same_priority)) (PreH9 : (prio_null_same_priority < 64)) (PreH10 : ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority)) (PreH11 : (0 <= slot_null_same_priority)) (PreH12 : (slot_null_same_priority <= 16)) (PreH13 : (0 <= requested_null_same_priority)) (PreH14 : (requested_null_same_priority <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_null_same_priority * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_21_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH5 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH6 : (func_capability_pre = slot_null_distinct_priorities)) (PreH7 : (rights_pre = requested_null_distinct_priorities)) (PreH8 : (0 <= dest_null_distinct_priorities)) (PreH9 : (dest_null_distinct_priorities < 64)) (PreH10 : (0 <= src_null_distinct_priorities)) (PreH11 : (src_null_distinct_priorities < 64)) (PreH12 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH13 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH15 : (0 <= slot_null_distinct_priorities)) (PreH16 : (slot_null_distinct_priorities <= 16)) (PreH17 : (0 <= requested_null_distinct_priorities)) (PreH18 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH19 : (target_null_distinct_priorities = 0)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_22_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH5 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH6 : (func_capability_pre = slot_null_distinct_priorities)) (PreH7 : (rights_pre = requested_null_distinct_priorities)) (PreH8 : (0 <= dest_null_distinct_priorities)) (PreH9 : (dest_null_distinct_priorities < 64)) (PreH10 : (0 <= src_null_distinct_priorities)) (PreH11 : (src_null_distinct_priorities < 64)) (PreH12 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH13 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH15 : (0 <= slot_null_distinct_priorities)) (PreH16 : (slot_null_distinct_priorities <= 16)) (PreH17 : (0 <= requested_null_distinct_priorities)) (PreH18 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH19 : (source_null_distinct_priorities = 0)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_23_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = prio_same_priority)) (PreH5 : (srcTask_Prio_pre = prio_same_priority)) (PreH6 : (func_capability_pre = slot_same_priority)) (PreH7 : (rights_pre = requested_same_priority)) (PreH8 : (0 <= prio_same_priority)) (PreH9 : (prio_same_priority < 64)) (PreH10 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH11 : (0 <= slot_same_priority)) (PreH12 : (slot_same_priority <= 16)) (PreH13 : (target_same_priority <> 0)) (PreH14 : (0 <= requested_same_priority)) (PreH15 : (requested_same_priority <= UINT_MAX)) (PreH16 : (0 <= word1_same_priority)) (PreH17 : (word1_same_priority <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_24_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = dest_shared_cspace)) (PreH5 : (srcTask_Prio_pre = src_shared_cspace)) (PreH6 : (func_capability_pre = slot_shared_cspace)) (PreH7 : (rights_pre = requested_shared_cspace)) (PreH8 : (0 <= dest_shared_cspace)) (PreH9 : (dest_shared_cspace < 64)) (PreH10 : (0 <= src_shared_cspace)) (PreH11 : (src_shared_cspace < 64)) (PreH12 : (dest_shared_cspace <> src_shared_cspace)) (PreH13 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH14 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH15 : (0 <= slot_shared_cspace)) (PreH16 : (slot_shared_cspace <= 16)) (PreH17 : (target_shared_cspace <> 0)) (PreH18 : (0 <= requested_shared_cspace)) (PreH19 : (requested_shared_cspace <= UINT_MAX)) (PreH20 : (0 <= word1_shared_cspace)) (PreH21 : (word1_shared_cspace <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_25_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH5 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH6 : (func_capability_pre = slot_distinct_cspaces)) (PreH7 : (rights_pre = requested_distinct_cspaces)) (PreH8 : (0 <= dest_distinct_cspaces)) (PreH9 : (dest_distinct_cspaces < 64)) (PreH10 : (0 <= src_distinct_cspaces)) (PreH11 : (src_distinct_cspaces < 64)) (PreH12 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH13 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH14 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH15 : (0 <= slot_distinct_cspaces)) (PreH16 : (slot_distinct_cspaces <= 16)) (PreH17 : (target_distinct_cspaces <> 0)) (PreH18 : (source_distinct_cspaces <> 0)) (PreH19 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH20 : (0 <= requested_distinct_cspaces)) (PreH21 : (requested_distinct_cspaces <= UINT_MAX)) (PreH22 : (0 <= src_word1_distinct_cspaces)) (PreH23 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_26_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH6 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH7 : (func_capability_pre = slot_distinct_cspaces)) (PreH8 : (rights_pre = requested_distinct_cspaces)) (PreH9 : (0 <= dest_distinct_cspaces)) (PreH10 : (dest_distinct_cspaces < 64)) (PreH11 : (0 <= src_distinct_cspaces)) (PreH12 : (src_distinct_cspaces < 64)) (PreH13 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH14 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH15 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH16 : (0 <= slot_distinct_cspaces)) (PreH17 : (slot_distinct_cspaces <= 16)) (PreH18 : (target_distinct_cspaces <> 0)) (PreH19 : (source_distinct_cspaces <> 0)) (PreH20 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH21 : (0 <= requested_distinct_cspaces)) (PreH22 : (requested_distinct_cspaces <= UINT_MAX)) (PreH23 : (0 <= src_word1_distinct_cspaces)) (PreH24 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_27_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_shared_cspace)) (PreH6 : (srcTask_Prio_pre = src_shared_cspace)) (PreH7 : (func_capability_pre = slot_shared_cspace)) (PreH8 : (rights_pre = requested_shared_cspace)) (PreH9 : (0 <= dest_shared_cspace)) (PreH10 : (dest_shared_cspace < 64)) (PreH11 : (0 <= src_shared_cspace)) (PreH12 : (src_shared_cspace < 64)) (PreH13 : (dest_shared_cspace <> src_shared_cspace)) (PreH14 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH15 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH16 : (0 <= slot_shared_cspace)) (PreH17 : (slot_shared_cspace <= 16)) (PreH18 : (target_shared_cspace <> 0)) (PreH19 : (0 <= requested_shared_cspace)) (PreH20 : (requested_shared_cspace <= UINT_MAX)) (PreH21 : (0 <= word1_shared_cspace)) (PreH22 : (word1_shared_cspace <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_28_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_same_priority)) (PreH7 : (func_capability_pre = slot_same_priority)) (PreH8 : (rights_pre = requested_same_priority)) (PreH9 : (0 <= prio_same_priority)) (PreH10 : (prio_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH12 : (0 <= slot_same_priority)) (PreH13 : (slot_same_priority <= 16)) (PreH14 : (target_same_priority <> 0)) (PreH15 : (0 <= requested_same_priority)) (PreH16 : (requested_same_priority <= UINT_MAX)) (PreH17 : (0 <= word1_same_priority)) (PreH18 : (word1_same_priority <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_29_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (source_null_distinct_priorities = 0)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_30_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (target_null_distinct_priorities = 0)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_31_null_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_null_same_priority: Z) (slot_null_same_priority: Z) (prio_null_same_priority: Z) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_null_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_null_same_priority)) (PreH7 : (func_capability_pre = slot_null_same_priority)) (PreH8 : (rights_pre = requested_null_same_priority)) (PreH9 : (0 <= prio_null_same_priority)) (PreH10 : (prio_null_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority)) (PreH12 : (0 <= slot_null_same_priority)) (PreH13 : (slot_null_same_priority <= 16)) (PreH14 : (0 <= requested_null_same_priority)) (PreH15 : (requested_null_same_priority <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (prio_null_same_priority * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_32_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_prio_invalid)) (PreH6 : (srcTask_Prio_pre = src_prio_invalid)) (PreH7 : (func_capability_pre = slot_prio_invalid)) (PreH8 : (rights_pre = requested_prio_invalid)) (PreH9 : (0 <= dest_prio_invalid)) (PreH10 : (dest_prio_invalid <= 255)) (PreH11 : (0 <= src_prio_invalid)) (PreH12 : (src_prio_invalid <= 255)) (PreH13 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH14 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH15 : (64 <= src_prio_invalid)) (PreH16 : (0 <= slot_prio_invalid)) (PreH17 : (slot_prio_invalid <= 16)) (PreH18 : (0 <= requested_prio_invalid)) (PreH19 : (requested_prio_invalid <= UINT_MAX)) ,
  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_33_null_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_null_same_priority: Z) (slot_null_same_priority: Z) (prio_null_same_priority: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_null_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_null_same_priority)) (PreH7 : (func_capability_pre = slot_null_same_priority)) (PreH8 : (rights_pre = requested_null_same_priority)) (PreH9 : (0 <= prio_null_same_priority)) (PreH10 : (prio_null_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority)) (PreH12 : (0 <= slot_null_same_priority)) (PreH13 : (slot_null_same_priority <= 16)) (PreH14 : (0 <= requested_null_same_priority)) (PreH15 : (requested_null_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> 0)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_34_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (target_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> source_null_distinct_priorities)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_35_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (source_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> 0)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_null_distinct_priorities)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_36_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_same_priority)) (PreH7 : (func_capability_pre = slot_same_priority)) (PreH8 : (rights_pre = requested_same_priority)) (PreH9 : (0 <= prio_same_priority)) (PreH10 : (prio_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH12 : (0 <= slot_same_priority)) (PreH13 : (slot_same_priority <= 16)) (PreH14 : (target_same_priority <> 0)) (PreH15 : (0 <= requested_same_priority)) (PreH16 : (requested_same_priority <= UINT_MAX)) (PreH17 : (0 <= word1_same_priority)) (PreH18 : (word1_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> target_same_priority)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_same_priority)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_37_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_shared_cspace)) (PreH6 : (srcTask_Prio_pre = src_shared_cspace)) (PreH7 : (func_capability_pre = slot_shared_cspace)) (PreH8 : (rights_pre = requested_shared_cspace)) (PreH9 : (0 <= dest_shared_cspace)) (PreH10 : (dest_shared_cspace < 64)) (PreH11 : (0 <= src_shared_cspace)) (PreH12 : (src_shared_cspace < 64)) (PreH13 : (dest_shared_cspace <> src_shared_cspace)) (PreH14 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH15 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH16 : (0 <= slot_shared_cspace)) (PreH17 : (slot_shared_cspace <= 16)) (PreH18 : (target_shared_cspace <> 0)) (PreH19 : (0 <= requested_shared_cspace)) (PreH20 : (requested_shared_cspace <= UINT_MAX)) (PreH21 : (0 <= word1_shared_cspace)) (PreH22 : (word1_shared_cspace <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> target_shared_cspace)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_shared_cspace)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_38_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH6 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH7 : (func_capability_pre = slot_distinct_cspaces)) (PreH8 : (rights_pre = requested_distinct_cspaces)) (PreH9 : (0 <= dest_distinct_cspaces)) (PreH10 : (dest_distinct_cspaces < 64)) (PreH11 : (0 <= src_distinct_cspaces)) (PreH12 : (src_distinct_cspaces < 64)) (PreH13 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH14 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH15 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH16 : (0 <= slot_distinct_cspaces)) (PreH17 : (slot_distinct_cspaces <= 16)) (PreH18 : (target_distinct_cspaces <> 0)) (PreH19 : (source_distinct_cspaces <> 0)) (PreH20 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH21 : (0 <= requested_distinct_cspaces)) (PreH22 : (requested_distinct_cspaces <= UINT_MAX)) (PreH23 : (0 <= src_word1_distinct_cspaces)) (PreH24 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> source_distinct_cspaces)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_distinct_cspaces)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_39_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (target_same_priority = 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = prio_same_priority)) (PreH7 : (srcTask_Prio_pre = prio_same_priority)) (PreH8 : (func_capability_pre = slot_same_priority)) (PreH9 : (rights_pre = requested_same_priority)) (PreH10 : (0 <= prio_same_priority)) (PreH11 : (prio_same_priority < 64)) (PreH12 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH13 : (0 <= slot_same_priority)) (PreH14 : (slot_same_priority <= 16)) (PreH15 : (target_same_priority <> 0)) (PreH16 : (0 <= requested_same_priority)) (PreH17 : (requested_same_priority <= UINT_MAX)) (PreH18 : (0 <= word1_same_priority)) (PreH19 : (word1_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> target_same_priority)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_same_priority)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_40_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (target_shared_cspace = 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = dest_shared_cspace)) (PreH7 : (srcTask_Prio_pre = src_shared_cspace)) (PreH8 : (func_capability_pre = slot_shared_cspace)) (PreH9 : (rights_pre = requested_shared_cspace)) (PreH10 : (0 <= dest_shared_cspace)) (PreH11 : (dest_shared_cspace < 64)) (PreH12 : (0 <= src_shared_cspace)) (PreH13 : (src_shared_cspace < 64)) (PreH14 : (dest_shared_cspace <> src_shared_cspace)) (PreH15 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH16 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH17 : (0 <= slot_shared_cspace)) (PreH18 : (slot_shared_cspace <= 16)) (PreH19 : (target_shared_cspace <> 0)) (PreH20 : (0 <= requested_shared_cspace)) (PreH21 : (requested_shared_cspace <= UINT_MAX)) (PreH22 : (0 <= word1_shared_cspace)) (PreH23 : (word1_shared_cspace <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> target_shared_cspace)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_shared_cspace)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_41_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (target_distinct_cspaces = 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH7 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH8 : (func_capability_pre = slot_distinct_cspaces)) (PreH9 : (rights_pre = requested_distinct_cspaces)) (PreH10 : (0 <= dest_distinct_cspaces)) (PreH11 : (dest_distinct_cspaces < 64)) (PreH12 : (0 <= src_distinct_cspaces)) (PreH13 : (src_distinct_cspaces < 64)) (PreH14 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH15 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH16 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH17 : (0 <= slot_distinct_cspaces)) (PreH18 : (slot_distinct_cspaces <= 16)) (PreH19 : (target_distinct_cspaces <> 0)) (PreH20 : (source_distinct_cspaces <> 0)) (PreH21 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH22 : (0 <= requested_distinct_cspaces)) (PreH23 : (requested_distinct_cspaces <= UINT_MAX)) (PreH24 : (0 <= src_word1_distinct_cspaces)) (PreH25 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> source_distinct_cspaces)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_distinct_cspaces)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_42_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (target_distinct_cspaces <> 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH7 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH8 : (func_capability_pre = slot_distinct_cspaces)) (PreH9 : (rights_pre = requested_distinct_cspaces)) (PreH10 : (0 <= dest_distinct_cspaces)) (PreH11 : (dest_distinct_cspaces < 64)) (PreH12 : (0 <= src_distinct_cspaces)) (PreH13 : (src_distinct_cspaces < 64)) (PreH14 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH15 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH16 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH17 : (0 <= slot_distinct_cspaces)) (PreH18 : (slot_distinct_cspaces <= 16)) (PreH19 : (target_distinct_cspaces <> 0)) (PreH20 : (source_distinct_cspaces <> 0)) (PreH21 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH22 : (0 <= requested_distinct_cspaces)) (PreH23 : (requested_distinct_cspaces <= UINT_MAX)) (PreH24 : (0 <= src_word1_distinct_cspaces)) (PreH25 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> source_distinct_cspaces)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_distinct_cspaces)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_43_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (target_shared_cspace <> 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = dest_shared_cspace)) (PreH7 : (srcTask_Prio_pre = src_shared_cspace)) (PreH8 : (func_capability_pre = slot_shared_cspace)) (PreH9 : (rights_pre = requested_shared_cspace)) (PreH10 : (0 <= dest_shared_cspace)) (PreH11 : (dest_shared_cspace < 64)) (PreH12 : (0 <= src_shared_cspace)) (PreH13 : (src_shared_cspace < 64)) (PreH14 : (dest_shared_cspace <> src_shared_cspace)) (PreH15 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH16 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH17 : (0 <= slot_shared_cspace)) (PreH18 : (slot_shared_cspace <= 16)) (PreH19 : (target_shared_cspace <> 0)) (PreH20 : (0 <= requested_shared_cspace)) (PreH21 : (requested_shared_cspace <= UINT_MAX)) (PreH22 : (0 <= word1_shared_cspace)) (PreH23 : (word1_shared_cspace <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> target_shared_cspace)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_shared_cspace)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_44_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (target_same_priority <> 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = prio_same_priority)) (PreH7 : (srcTask_Prio_pre = prio_same_priority)) (PreH8 : (func_capability_pre = slot_same_priority)) (PreH9 : (rights_pre = requested_same_priority)) (PreH10 : (0 <= prio_same_priority)) (PreH11 : (prio_same_priority < 64)) (PreH12 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH13 : (0 <= slot_same_priority)) (PreH14 : (slot_same_priority <= 16)) (PreH15 : (target_same_priority <> 0)) (PreH16 : (0 <= requested_same_priority)) (PreH17 : (requested_same_priority <= UINT_MAX)) (PreH18 : (0 <= word1_same_priority)) (PreH19 : (word1_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> target_same_priority)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_same_priority)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_45_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (target_null_distinct_priorities <> 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH7 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH8 : (func_capability_pre = slot_null_distinct_priorities)) (PreH9 : (rights_pre = requested_null_distinct_priorities)) (PreH10 : (0 <= dest_null_distinct_priorities)) (PreH11 : (dest_null_distinct_priorities < 64)) (PreH12 : (0 <= src_null_distinct_priorities)) (PreH13 : (src_null_distinct_priorities < 64)) (PreH14 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH16 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH17 : (0 <= slot_null_distinct_priorities)) (PreH18 : (slot_null_distinct_priorities <= 16)) (PreH19 : (0 <= requested_null_distinct_priorities)) (PreH20 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH21 : (source_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> 0)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_null_distinct_priorities)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Mint_safety_wit_46_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (source_distinct_cspaces = 0)) (PreH2 : (target_distinct_cspaces <> 0)) (PreH3 : (srcTask_Prio_pre < 64)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre <= 16)) (PreH6 : (0 <= func_capability_pre)) (PreH7 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH8 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH9 : (func_capability_pre = slot_distinct_cspaces)) (PreH10 : (rights_pre = requested_distinct_cspaces)) (PreH11 : (0 <= dest_distinct_cspaces)) (PreH12 : (dest_distinct_cspaces < 64)) (PreH13 : (0 <= src_distinct_cspaces)) (PreH14 : (src_distinct_cspaces < 64)) (PreH15 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH16 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH17 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH18 : (0 <= slot_distinct_cspaces)) (PreH19 : (slot_distinct_cspaces <= 16)) (PreH20 : (target_distinct_cspaces <> 0)) (PreH21 : (source_distinct_cspaces <> 0)) (PreH22 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH23 : (0 <= requested_distinct_cspaces)) (PreH24 : (requested_distinct_cspaces <= UINT_MAX)) (PreH25 : (0 <= src_word1_distinct_cspaces)) (PreH26 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> source_distinct_cspaces)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_distinct_cspaces)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_47_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (target_shared_cspace = 0)) (PreH2 : (target_shared_cspace <> 0)) (PreH3 : (srcTask_Prio_pre < 64)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre <= 16)) (PreH6 : (0 <= func_capability_pre)) (PreH7 : (destTask_Prio_pre = dest_shared_cspace)) (PreH8 : (srcTask_Prio_pre = src_shared_cspace)) (PreH9 : (func_capability_pre = slot_shared_cspace)) (PreH10 : (rights_pre = requested_shared_cspace)) (PreH11 : (0 <= dest_shared_cspace)) (PreH12 : (dest_shared_cspace < 64)) (PreH13 : (0 <= src_shared_cspace)) (PreH14 : (src_shared_cspace < 64)) (PreH15 : (dest_shared_cspace <> src_shared_cspace)) (PreH16 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH17 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH18 : (0 <= slot_shared_cspace)) (PreH19 : (slot_shared_cspace <= 16)) (PreH20 : (target_shared_cspace <> 0)) (PreH21 : (0 <= requested_shared_cspace)) (PreH22 : (requested_shared_cspace <= UINT_MAX)) (PreH23 : (0 <= word1_shared_cspace)) (PreH24 : (word1_shared_cspace <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> target_shared_cspace)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_shared_cspace)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ False ”
.

Definition ucos_CNode_Mint_safety_wit_48_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (target_same_priority = 0)) (PreH2 : (target_same_priority <> 0)) (PreH3 : (srcTask_Prio_pre < 64)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre <= 16)) (PreH6 : (0 <= func_capability_pre)) (PreH7 : (destTask_Prio_pre = prio_same_priority)) (PreH8 : (srcTask_Prio_pre = prio_same_priority)) (PreH9 : (func_capability_pre = slot_same_priority)) (PreH10 : (rights_pre = requested_same_priority)) (PreH11 : (0 <= prio_same_priority)) (PreH12 : (prio_same_priority < 64)) (PreH13 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH14 : (0 <= slot_same_priority)) (PreH15 : (slot_same_priority <= 16)) (PreH16 : (target_same_priority <> 0)) (PreH17 : (0 <= requested_same_priority)) (PreH18 : (requested_same_priority <= UINT_MAX)) (PreH19 : (0 <= word1_same_priority)) (PreH20 : (word1_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((( &( "cap2" ) )) # Ptr  |->_)
  **  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace2" ) )) # Ptr  |-> target_same_priority)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> target_same_priority)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "srcTask_Prio" ) )) # UChar  |-> srcTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  ((( &( "rights" ) )) # UInt  |-> rights_pre)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ False ”
.

Definition ucos_CNode_Mint_return_wit_1_distinct_cspaces := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_word1_distinct_cspaces <> rights_pre)) (PreH2 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH3 : (src_kind_distinct_cspaces = 1)) (PreH4 : (source_distinct_cspaces <> 0)) (PreH5 : (target_distinct_cspaces <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH11 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH12 : (func_capability_pre = slot_distinct_cspaces)) (PreH13 : (rights_pre = requested_distinct_cspaces)) (PreH14 : (0 <= dest_distinct_cspaces)) (PreH15 : (dest_distinct_cspaces < 64)) (PreH16 : (0 <= src_distinct_cspaces)) (PreH17 : (src_distinct_cspaces < 64)) (PreH18 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH20 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH21 : (0 <= slot_distinct_cspaces)) (PreH22 : (slot_distinct_cspaces <= 16)) (PreH23 : (target_distinct_cspaces <> 0)) (PreH24 : (source_distinct_cspaces <> 0)) (PreH25 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH26 : (0 <= requested_distinct_cspaces)) (PreH27 : (requested_distinct_cspaces <= UINT_MAX)) (PreH28 : (0 <= src_word1_distinct_cspaces)) (PreH29 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> rights_pre)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 0 requested_distinct_cspaces src_kind_distinct_cspaces src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <= UINT_MAX)) (PreH2 : (1 <= UINT_MAX)) (PreH3 : (src_word0_distinct_cspaces <= UINT_MAX)) (PreH4 : (rights_pre <= UINT_MAX)) (PreH5 : (src_kind_distinct_cspaces >= 0)) (PreH6 : (src_word1_distinct_cspaces >= 0)) (PreH7 : (1 >= 0)) (PreH8 : (src_word0_distinct_cspaces >= 0)) (PreH9 : (rights_pre >= 0)) (PreH10 : (src_word1_distinct_cspaces <> rights_pre)) (PreH11 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH12 : (src_kind_distinct_cspaces = 1)) (PreH13 : (source_distinct_cspaces <> 0)) (PreH14 : (target_distinct_cspaces <> 0)) (PreH15 : (srcTask_Prio_pre < 64)) (PreH16 : (destTask_Prio_pre < 64)) (PreH17 : (func_capability_pre <= 16)) (PreH18 : (0 <= func_capability_pre)) (PreH19 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH20 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH21 : (func_capability_pre = slot_distinct_cspaces)) (PreH22 : (rights_pre = requested_distinct_cspaces)) (PreH23 : (0 <= dest_distinct_cspaces)) (PreH24 : (dest_distinct_cspaces < 64)) (PreH25 : (0 <= src_distinct_cspaces)) (PreH26 : (src_distinct_cspaces < 64)) (PreH27 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH28 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH29 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH30 : (0 <= slot_distinct_cspaces)) (PreH31 : (slot_distinct_cspaces <= 16)) (PreH32 : (target_distinct_cspaces <> 0)) (PreH33 : (source_distinct_cspaces <> 0)) (PreH34 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH35 : (0 <= requested_distinct_cspaces)) (PreH36 : (requested_distinct_cspaces <= UINT_MAX)) (PreH37 : (0 <= src_word1_distinct_cspaces)) (PreH38 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 0 rights_pre 1 src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces 1 src_word0_distinct_cspaces rights_pre ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_1_distinct_cspaces_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <= UINT_MAX)) (PreH2 : (1 <= UINT_MAX)) (PreH3 : (src_word0_distinct_cspaces <= UINT_MAX)) (PreH4 : (rights_pre <= UINT_MAX)) (PreH5 : (src_kind_distinct_cspaces >= 0)) (PreH6 : (src_word1_distinct_cspaces >= 0)) (PreH7 : (1 >= 0)) (PreH8 : (src_word0_distinct_cspaces >= 0)) (PreH9 : (rights_pre >= 0)) (PreH10 : (src_word1_distinct_cspaces <> rights_pre)) (PreH11 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH12 : (src_kind_distinct_cspaces = 1)) (PreH13 : (source_distinct_cspaces <> 0)) (PreH14 : (target_distinct_cspaces <> 0)) (PreH15 : (srcTask_Prio_pre < 64)) (PreH16 : (destTask_Prio_pre < 64)) (PreH17 : (func_capability_pre <= 16)) (PreH18 : (0 <= func_capability_pre)) (PreH19 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH20 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH21 : (func_capability_pre = slot_distinct_cspaces)) (PreH22 : (rights_pre = requested_distinct_cspaces)) (PreH23 : (0 <= dest_distinct_cspaces)) (PreH24 : (dest_distinct_cspaces < 64)) (PreH25 : (0 <= src_distinct_cspaces)) (PreH26 : (src_distinct_cspaces < 64)) (PreH27 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH28 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH29 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH30 : (0 <= slot_distinct_cspaces)) (PreH31 : (slot_distinct_cspaces <= 16)) (PreH32 : (target_distinct_cspaces <> 0)) (PreH33 : (source_distinct_cspaces <> 0)) (PreH34 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH35 : (0 <= requested_distinct_cspaces)) (PreH36 : (requested_distinct_cspaces <= UINT_MAX)) (PreH37 : (0 <= src_word1_distinct_cspaces)) (PreH38 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (mint_cap_transition 0 rights_pre 1 src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces 1 src_word0_distinct_cspaces rights_pre )
.

Definition ucos_CNode_Mint_return_wit_2_shared_cspace := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (word1_shared_cspace <> rights_pre)) (PreH2 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) = 0)) (PreH3 : (old_kind_shared_cspace = 1)) (PreH4 : (target_shared_cspace <> 0)) (PreH5 : (target_shared_cspace <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_shared_cspace)) (PreH11 : (srcTask_Prio_pre = src_shared_cspace)) (PreH12 : (func_capability_pre = slot_shared_cspace)) (PreH13 : (rights_pre = requested_shared_cspace)) (PreH14 : (0 <= dest_shared_cspace)) (PreH15 : (dest_shared_cspace < 64)) (PreH16 : (0 <= src_shared_cspace)) (PreH17 : (src_shared_cspace < 64)) (PreH18 : (dest_shared_cspace <> src_shared_cspace)) (PreH19 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH20 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH21 : (0 <= slot_shared_cspace)) (PreH22 : (slot_shared_cspace <= 16)) (PreH23 : (target_shared_cspace <> 0)) (PreH24 : (0 <= requested_shared_cspace)) (PreH25 : (requested_shared_cspace <= UINT_MAX)) (PreH26 : (0 <= word1_shared_cspace)) (PreH27 : (word1_shared_cspace <= UINT_MAX)) ,
  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> rights_pre)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 0 requested_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (1 <= UINT_MAX)) (PreH2 : (rights_pre <= UINT_MAX)) (PreH3 : (word0_shared_cspace <= UINT_MAX)) (PreH4 : (1 >= 0)) (PreH5 : (rights_pre >= 0)) (PreH6 : (word0_shared_cspace >= 0)) (PreH7 : (word1_shared_cspace <> rights_pre)) (PreH8 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) = 0)) (PreH9 : (old_kind_shared_cspace = 1)) (PreH10 : (target_shared_cspace <> 0)) (PreH11 : (target_shared_cspace <> 0)) (PreH12 : (srcTask_Prio_pre < 64)) (PreH13 : (destTask_Prio_pre < 64)) (PreH14 : (func_capability_pre <= 16)) (PreH15 : (0 <= func_capability_pre)) (PreH16 : (destTask_Prio_pre = dest_shared_cspace)) (PreH17 : (srcTask_Prio_pre = src_shared_cspace)) (PreH18 : (func_capability_pre = slot_shared_cspace)) (PreH19 : (rights_pre = requested_shared_cspace)) (PreH20 : (0 <= dest_shared_cspace)) (PreH21 : (dest_shared_cspace < 64)) (PreH22 : (0 <= src_shared_cspace)) (PreH23 : (src_shared_cspace < 64)) (PreH24 : (dest_shared_cspace <> src_shared_cspace)) (PreH25 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH26 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH27 : (0 <= slot_shared_cspace)) (PreH28 : (slot_shared_cspace <= 16)) (PreH29 : (target_shared_cspace <> 0)) (PreH30 : (0 <= requested_shared_cspace)) (PreH31 : (requested_shared_cspace <= UINT_MAX)) (PreH32 : (0 <= word1_shared_cspace)) (PreH33 : (word1_shared_cspace <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 0 rights_pre 1 word0_shared_cspace word1_shared_cspace 1 word0_shared_cspace word1_shared_cspace 1 word0_shared_cspace rights_pre ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_2_shared_cspace_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (1 <= UINT_MAX)) (PreH2 : (rights_pre <= UINT_MAX)) (PreH3 : (word0_shared_cspace <= UINT_MAX)) (PreH4 : (1 >= 0)) (PreH5 : (rights_pre >= 0)) (PreH6 : (word0_shared_cspace >= 0)) (PreH7 : (word1_shared_cspace <> rights_pre)) (PreH8 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) = 0)) (PreH9 : (old_kind_shared_cspace = 1)) (PreH10 : (target_shared_cspace <> 0)) (PreH11 : (target_shared_cspace <> 0)) (PreH12 : (srcTask_Prio_pre < 64)) (PreH13 : (destTask_Prio_pre < 64)) (PreH14 : (func_capability_pre <= 16)) (PreH15 : (0 <= func_capability_pre)) (PreH16 : (destTask_Prio_pre = dest_shared_cspace)) (PreH17 : (srcTask_Prio_pre = src_shared_cspace)) (PreH18 : (func_capability_pre = slot_shared_cspace)) (PreH19 : (rights_pre = requested_shared_cspace)) (PreH20 : (0 <= dest_shared_cspace)) (PreH21 : (dest_shared_cspace < 64)) (PreH22 : (0 <= src_shared_cspace)) (PreH23 : (src_shared_cspace < 64)) (PreH24 : (dest_shared_cspace <> src_shared_cspace)) (PreH25 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH26 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH27 : (0 <= slot_shared_cspace)) (PreH28 : (slot_shared_cspace <= 16)) (PreH29 : (target_shared_cspace <> 0)) (PreH30 : (0 <= requested_shared_cspace)) (PreH31 : (requested_shared_cspace <= UINT_MAX)) (PreH32 : (0 <= word1_shared_cspace)) (PreH33 : (word1_shared_cspace <= UINT_MAX)) ,
  (mint_cap_transition 0 rights_pre 1 word0_shared_cspace word1_shared_cspace 1 word0_shared_cspace word1_shared_cspace 1 word0_shared_cspace rights_pre )
.

Definition ucos_CNode_Mint_return_wit_3_same_priority := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (word1_same_priority <> rights_pre)) (PreH2 : ((Z.land (Z.lnot word1_same_priority) rights_pre) = 0)) (PreH3 : (old_kind_same_priority = 1)) (PreH4 : (target_same_priority <> 0)) (PreH5 : (target_same_priority <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = prio_same_priority)) (PreH11 : (srcTask_Prio_pre = prio_same_priority)) (PreH12 : (func_capability_pre = slot_same_priority)) (PreH13 : (rights_pre = requested_same_priority)) (PreH14 : (0 <= prio_same_priority)) (PreH15 : (prio_same_priority < 64)) (PreH16 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH17 : (0 <= slot_same_priority)) (PreH18 : (slot_same_priority <= 16)) (PreH19 : (target_same_priority <> 0)) (PreH20 : (0 <= requested_same_priority)) (PreH21 : (requested_same_priority <= UINT_MAX)) (PreH22 : (0 <= word1_same_priority)) (PreH23 : (word1_same_priority <= UINT_MAX)) ,
  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> rights_pre)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 0 requested_same_priority old_kind_same_priority word0_same_priority word1_same_priority old_kind_same_priority word0_same_priority word1_same_priority new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (1 <= UINT_MAX)) (PreH2 : (rights_pre <= UINT_MAX)) (PreH3 : (word0_same_priority <= UINT_MAX)) (PreH4 : (1 >= 0)) (PreH5 : (rights_pre >= 0)) (PreH6 : (word0_same_priority >= 0)) (PreH7 : (word1_same_priority <> rights_pre)) (PreH8 : ((Z.land (Z.lnot word1_same_priority) rights_pre) = 0)) (PreH9 : (old_kind_same_priority = 1)) (PreH10 : (target_same_priority <> 0)) (PreH11 : (target_same_priority <> 0)) (PreH12 : (srcTask_Prio_pre < 64)) (PreH13 : (destTask_Prio_pre < 64)) (PreH14 : (func_capability_pre <= 16)) (PreH15 : (0 <= func_capability_pre)) (PreH16 : (destTask_Prio_pre = prio_same_priority)) (PreH17 : (srcTask_Prio_pre = prio_same_priority)) (PreH18 : (func_capability_pre = slot_same_priority)) (PreH19 : (rights_pre = requested_same_priority)) (PreH20 : (0 <= prio_same_priority)) (PreH21 : (prio_same_priority < 64)) (PreH22 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH23 : (0 <= slot_same_priority)) (PreH24 : (slot_same_priority <= 16)) (PreH25 : (target_same_priority <> 0)) (PreH26 : (0 <= requested_same_priority)) (PreH27 : (requested_same_priority <= UINT_MAX)) (PreH28 : (0 <= word1_same_priority)) (PreH29 : (word1_same_priority <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 0 rights_pre 1 word0_same_priority word1_same_priority 1 word0_same_priority word1_same_priority 1 word0_same_priority rights_pre ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_3_same_priority_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (1 <= UINT_MAX)) (PreH2 : (rights_pre <= UINT_MAX)) (PreH3 : (word0_same_priority <= UINT_MAX)) (PreH4 : (1 >= 0)) (PreH5 : (rights_pre >= 0)) (PreH6 : (word0_same_priority >= 0)) (PreH7 : (word1_same_priority <> rights_pre)) (PreH8 : ((Z.land (Z.lnot word1_same_priority) rights_pre) = 0)) (PreH9 : (old_kind_same_priority = 1)) (PreH10 : (target_same_priority <> 0)) (PreH11 : (target_same_priority <> 0)) (PreH12 : (srcTask_Prio_pre < 64)) (PreH13 : (destTask_Prio_pre < 64)) (PreH14 : (func_capability_pre <= 16)) (PreH15 : (0 <= func_capability_pre)) (PreH16 : (destTask_Prio_pre = prio_same_priority)) (PreH17 : (srcTask_Prio_pre = prio_same_priority)) (PreH18 : (func_capability_pre = slot_same_priority)) (PreH19 : (rights_pre = requested_same_priority)) (PreH20 : (0 <= prio_same_priority)) (PreH21 : (prio_same_priority < 64)) (PreH22 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH23 : (0 <= slot_same_priority)) (PreH24 : (slot_same_priority <= 16)) (PreH25 : (target_same_priority <> 0)) (PreH26 : (0 <= requested_same_priority)) (PreH27 : (requested_same_priority <= UINT_MAX)) (PreH28 : (0 <= word1_same_priority)) (PreH29 : (word1_same_priority <= UINT_MAX)) ,
  (mint_cap_transition 0 rights_pre 1 word0_same_priority word1_same_priority 1 word0_same_priority word1_same_priority 1 word0_same_priority rights_pre )
.

Definition ucos_CNode_Mint_return_wit_4_distinct_cspaces := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) <> 0)) (PreH2 : (src_kind_distinct_cspaces = 1)) (PreH3 : (source_distinct_cspaces <> 0)) (PreH4 : (target_distinct_cspaces <> 0)) (PreH5 : (srcTask_Prio_pre < 64)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (func_capability_pre <= 16)) (PreH8 : (0 <= func_capability_pre)) (PreH9 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH10 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH11 : (func_capability_pre = slot_distinct_cspaces)) (PreH12 : (rights_pre = requested_distinct_cspaces)) (PreH13 : (0 <= dest_distinct_cspaces)) (PreH14 : (dest_distinct_cspaces < 64)) (PreH15 : (0 <= src_distinct_cspaces)) (PreH16 : (src_distinct_cspaces < 64)) (PreH17 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH18 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH20 : (0 <= slot_distinct_cspaces)) (PreH21 : (slot_distinct_cspaces <= 16)) (PreH22 : (target_distinct_cspaces <> 0)) (PreH23 : (source_distinct_cspaces <> 0)) (PreH24 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH25 : (0 <= requested_distinct_cspaces)) (PreH26 : (requested_distinct_cspaces <= UINT_MAX)) (PreH27 : (0 <= src_word1_distinct_cspaces)) (PreH28 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_distinct_cspaces src_kind_distinct_cspaces src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <= UINT_MAX)) (PreH2 : (src_kind_distinct_cspaces >= 0)) (PreH3 : (src_word1_distinct_cspaces >= 0)) (PreH4 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) <> 0)) (PreH5 : (src_kind_distinct_cspaces = 1)) (PreH6 : (source_distinct_cspaces <> 0)) (PreH7 : (target_distinct_cspaces <> 0)) (PreH8 : (srcTask_Prio_pre < 64)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (func_capability_pre <= 16)) (PreH11 : (0 <= func_capability_pre)) (PreH12 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH13 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH14 : (func_capability_pre = slot_distinct_cspaces)) (PreH15 : (rights_pre = requested_distinct_cspaces)) (PreH16 : (0 <= dest_distinct_cspaces)) (PreH17 : (dest_distinct_cspaces < 64)) (PreH18 : (0 <= src_distinct_cspaces)) (PreH19 : (src_distinct_cspaces < 64)) (PreH20 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH21 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH22 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH23 : (0 <= slot_distinct_cspaces)) (PreH24 : (slot_distinct_cspaces <= 16)) (PreH25 : (target_distinct_cspaces <> 0)) (PreH26 : (source_distinct_cspaces <> 0)) (PreH27 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH28 : (0 <= requested_distinct_cspaces)) (PreH29 : (requested_distinct_cspaces <= UINT_MAX)) (PreH30 : (0 <= src_word1_distinct_cspaces)) (PreH31 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre 1 src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_4_distinct_cspaces_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <= UINT_MAX)) (PreH2 : (src_kind_distinct_cspaces >= 0)) (PreH3 : (src_word1_distinct_cspaces >= 0)) (PreH4 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) <> 0)) (PreH5 : (src_kind_distinct_cspaces = 1)) (PreH6 : (source_distinct_cspaces <> 0)) (PreH7 : (target_distinct_cspaces <> 0)) (PreH8 : (srcTask_Prio_pre < 64)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (func_capability_pre <= 16)) (PreH11 : (0 <= func_capability_pre)) (PreH12 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH13 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH14 : (func_capability_pre = slot_distinct_cspaces)) (PreH15 : (rights_pre = requested_distinct_cspaces)) (PreH16 : (0 <= dest_distinct_cspaces)) (PreH17 : (dest_distinct_cspaces < 64)) (PreH18 : (0 <= src_distinct_cspaces)) (PreH19 : (src_distinct_cspaces < 64)) (PreH20 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH21 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH22 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH23 : (0 <= slot_distinct_cspaces)) (PreH24 : (slot_distinct_cspaces <= 16)) (PreH25 : (target_distinct_cspaces <> 0)) (PreH26 : (source_distinct_cspaces <> 0)) (PreH27 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH28 : (0 <= requested_distinct_cspaces)) (PreH29 : (requested_distinct_cspaces <= UINT_MAX)) (PreH30 : (0 <= src_word1_distinct_cspaces)) (PreH31 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre 1 src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces )
.

Definition ucos_CNode_Mint_return_wit_5_shared_cspace := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) <> 0)) (PreH2 : (old_kind_shared_cspace = 1)) (PreH3 : (target_shared_cspace <> 0)) (PreH4 : (target_shared_cspace <> 0)) (PreH5 : (srcTask_Prio_pre < 64)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (func_capability_pre <= 16)) (PreH8 : (0 <= func_capability_pre)) (PreH9 : (destTask_Prio_pre = dest_shared_cspace)) (PreH10 : (srcTask_Prio_pre = src_shared_cspace)) (PreH11 : (func_capability_pre = slot_shared_cspace)) (PreH12 : (rights_pre = requested_shared_cspace)) (PreH13 : (0 <= dest_shared_cspace)) (PreH14 : (dest_shared_cspace < 64)) (PreH15 : (0 <= src_shared_cspace)) (PreH16 : (src_shared_cspace < 64)) (PreH17 : (dest_shared_cspace <> src_shared_cspace)) (PreH18 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH19 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH20 : (0 <= slot_shared_cspace)) (PreH21 : (slot_shared_cspace <= 16)) (PreH22 : (target_shared_cspace <> 0)) (PreH23 : (0 <= requested_shared_cspace)) (PreH24 : (requested_shared_cspace <= UINT_MAX)) (PreH25 : (0 <= word1_shared_cspace)) (PreH26 : (word1_shared_cspace <= UINT_MAX)) ,
  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (old_kind_shared_cspace <= UINT_MAX)) (PreH2 : (old_kind_shared_cspace >= 0)) (PreH3 : (word1_shared_cspace >= 0)) (PreH4 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) <> 0)) (PreH5 : (old_kind_shared_cspace = 1)) (PreH6 : (target_shared_cspace <> 0)) (PreH7 : (target_shared_cspace <> 0)) (PreH8 : (srcTask_Prio_pre < 64)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (func_capability_pre <= 16)) (PreH11 : (0 <= func_capability_pre)) (PreH12 : (destTask_Prio_pre = dest_shared_cspace)) (PreH13 : (srcTask_Prio_pre = src_shared_cspace)) (PreH14 : (func_capability_pre = slot_shared_cspace)) (PreH15 : (rights_pre = requested_shared_cspace)) (PreH16 : (0 <= dest_shared_cspace)) (PreH17 : (dest_shared_cspace < 64)) (PreH18 : (0 <= src_shared_cspace)) (PreH19 : (src_shared_cspace < 64)) (PreH20 : (dest_shared_cspace <> src_shared_cspace)) (PreH21 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH22 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH23 : (0 <= slot_shared_cspace)) (PreH24 : (slot_shared_cspace <= 16)) (PreH25 : (target_shared_cspace <> 0)) (PreH26 : (0 <= requested_shared_cspace)) (PreH27 : (requested_shared_cspace <= UINT_MAX)) (PreH28 : (0 <= word1_shared_cspace)) (PreH29 : (word1_shared_cspace <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre 1 word0_shared_cspace word1_shared_cspace 1 word0_shared_cspace word1_shared_cspace 1 word0_shared_cspace word1_shared_cspace ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_5_shared_cspace_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (old_kind_shared_cspace <= UINT_MAX)) (PreH2 : (old_kind_shared_cspace >= 0)) (PreH3 : (word1_shared_cspace >= 0)) (PreH4 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) <> 0)) (PreH5 : (old_kind_shared_cspace = 1)) (PreH6 : (target_shared_cspace <> 0)) (PreH7 : (target_shared_cspace <> 0)) (PreH8 : (srcTask_Prio_pre < 64)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (func_capability_pre <= 16)) (PreH11 : (0 <= func_capability_pre)) (PreH12 : (destTask_Prio_pre = dest_shared_cspace)) (PreH13 : (srcTask_Prio_pre = src_shared_cspace)) (PreH14 : (func_capability_pre = slot_shared_cspace)) (PreH15 : (rights_pre = requested_shared_cspace)) (PreH16 : (0 <= dest_shared_cspace)) (PreH17 : (dest_shared_cspace < 64)) (PreH18 : (0 <= src_shared_cspace)) (PreH19 : (src_shared_cspace < 64)) (PreH20 : (dest_shared_cspace <> src_shared_cspace)) (PreH21 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH22 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH23 : (0 <= slot_shared_cspace)) (PreH24 : (slot_shared_cspace <= 16)) (PreH25 : (target_shared_cspace <> 0)) (PreH26 : (0 <= requested_shared_cspace)) (PreH27 : (requested_shared_cspace <= UINT_MAX)) (PreH28 : (0 <= word1_shared_cspace)) (PreH29 : (word1_shared_cspace <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre 1 word0_shared_cspace word1_shared_cspace 1 word0_shared_cspace word1_shared_cspace 1 word0_shared_cspace word1_shared_cspace )
.

Definition ucos_CNode_Mint_return_wit_6_same_priority := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : ((Z.land (Z.lnot word1_same_priority) rights_pre) <> 0)) (PreH2 : (old_kind_same_priority = 1)) (PreH3 : (target_same_priority <> 0)) (PreH4 : (target_same_priority <> 0)) (PreH5 : (srcTask_Prio_pre < 64)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (func_capability_pre <= 16)) (PreH8 : (0 <= func_capability_pre)) (PreH9 : (destTask_Prio_pre = prio_same_priority)) (PreH10 : (srcTask_Prio_pre = prio_same_priority)) (PreH11 : (func_capability_pre = slot_same_priority)) (PreH12 : (rights_pre = requested_same_priority)) (PreH13 : (0 <= prio_same_priority)) (PreH14 : (prio_same_priority < 64)) (PreH15 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH16 : (0 <= slot_same_priority)) (PreH17 : (slot_same_priority <= 16)) (PreH18 : (target_same_priority <> 0)) (PreH19 : (0 <= requested_same_priority)) (PreH20 : (requested_same_priority <= UINT_MAX)) (PreH21 : (0 <= word1_same_priority)) (PreH22 : (word1_same_priority <= UINT_MAX)) ,
  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_same_priority old_kind_same_priority word0_same_priority word1_same_priority old_kind_same_priority word0_same_priority word1_same_priority new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (old_kind_same_priority <= UINT_MAX)) (PreH2 : (old_kind_same_priority >= 0)) (PreH3 : (word1_same_priority >= 0)) (PreH4 : ((Z.land (Z.lnot word1_same_priority) rights_pre) <> 0)) (PreH5 : (old_kind_same_priority = 1)) (PreH6 : (target_same_priority <> 0)) (PreH7 : (target_same_priority <> 0)) (PreH8 : (srcTask_Prio_pre < 64)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (func_capability_pre <= 16)) (PreH11 : (0 <= func_capability_pre)) (PreH12 : (destTask_Prio_pre = prio_same_priority)) (PreH13 : (srcTask_Prio_pre = prio_same_priority)) (PreH14 : (func_capability_pre = slot_same_priority)) (PreH15 : (rights_pre = requested_same_priority)) (PreH16 : (0 <= prio_same_priority)) (PreH17 : (prio_same_priority < 64)) (PreH18 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH19 : (0 <= slot_same_priority)) (PreH20 : (slot_same_priority <= 16)) (PreH21 : (target_same_priority <> 0)) (PreH22 : (0 <= requested_same_priority)) (PreH23 : (requested_same_priority <= UINT_MAX)) (PreH24 : (0 <= word1_same_priority)) (PreH25 : (word1_same_priority <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre 1 word0_same_priority word1_same_priority 1 word0_same_priority word1_same_priority 1 word0_same_priority word1_same_priority ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_6_same_priority_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (old_kind_same_priority <= UINT_MAX)) (PreH2 : (old_kind_same_priority >= 0)) (PreH3 : (word1_same_priority >= 0)) (PreH4 : ((Z.land (Z.lnot word1_same_priority) rights_pre) <> 0)) (PreH5 : (old_kind_same_priority = 1)) (PreH6 : (target_same_priority <> 0)) (PreH7 : (target_same_priority <> 0)) (PreH8 : (srcTask_Prio_pre < 64)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (func_capability_pre <= 16)) (PreH11 : (0 <= func_capability_pre)) (PreH12 : (destTask_Prio_pre = prio_same_priority)) (PreH13 : (srcTask_Prio_pre = prio_same_priority)) (PreH14 : (func_capability_pre = slot_same_priority)) (PreH15 : (rights_pre = requested_same_priority)) (PreH16 : (0 <= prio_same_priority)) (PreH17 : (prio_same_priority < 64)) (PreH18 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH19 : (0 <= slot_same_priority)) (PreH20 : (slot_same_priority <= 16)) (PreH21 : (target_same_priority <> 0)) (PreH22 : (0 <= requested_same_priority)) (PreH23 : (requested_same_priority <= UINT_MAX)) (PreH24 : (0 <= word1_same_priority)) (PreH25 : (word1_same_priority <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre 1 word0_same_priority word1_same_priority 1 word0_same_priority word1_same_priority 1 word0_same_priority word1_same_priority )
.

Definition ucos_CNode_Mint_return_wit_7_same_priority := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (old_kind_same_priority <> 1)) (PreH2 : (target_same_priority <> 0)) (PreH3 : (target_same_priority <> 0)) (PreH4 : (srcTask_Prio_pre < 64)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (func_capability_pre <= 16)) (PreH7 : (0 <= func_capability_pre)) (PreH8 : (destTask_Prio_pre = prio_same_priority)) (PreH9 : (srcTask_Prio_pre = prio_same_priority)) (PreH10 : (func_capability_pre = slot_same_priority)) (PreH11 : (rights_pre = requested_same_priority)) (PreH12 : (0 <= prio_same_priority)) (PreH13 : (prio_same_priority < 64)) (PreH14 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH15 : (0 <= slot_same_priority)) (PreH16 : (slot_same_priority <= 16)) (PreH17 : (target_same_priority <> 0)) (PreH18 : (0 <= requested_same_priority)) (PreH19 : (requested_same_priority <= UINT_MAX)) (PreH20 : (0 <= word1_same_priority)) (PreH21 : (word1_same_priority <= UINT_MAX)) ,
  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_same_priority old_kind_same_priority word0_same_priority word1_same_priority old_kind_same_priority word0_same_priority word1_same_priority new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (old_kind_same_priority <= UINT_MAX)) (PreH2 : (old_kind_same_priority >= 0)) (PreH3 : (old_kind_same_priority <> 1)) (PreH4 : (target_same_priority <> 0)) (PreH5 : (target_same_priority <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = prio_same_priority)) (PreH11 : (srcTask_Prio_pre = prio_same_priority)) (PreH12 : (func_capability_pre = slot_same_priority)) (PreH13 : (rights_pre = requested_same_priority)) (PreH14 : (0 <= prio_same_priority)) (PreH15 : (prio_same_priority < 64)) (PreH16 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH17 : (0 <= slot_same_priority)) (PreH18 : (slot_same_priority <= 16)) (PreH19 : (target_same_priority <> 0)) (PreH20 : (0 <= requested_same_priority)) (PreH21 : (requested_same_priority <= UINT_MAX)) (PreH22 : (0 <= word1_same_priority)) (PreH23 : (word1_same_priority <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre old_kind_same_priority word0_same_priority word1_same_priority old_kind_same_priority word0_same_priority word1_same_priority old_kind_same_priority word0_same_priority word1_same_priority ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_7_same_priority_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (old_kind_same_priority <= UINT_MAX)) (PreH2 : (old_kind_same_priority >= 0)) (PreH3 : (old_kind_same_priority <> 1)) (PreH4 : (target_same_priority <> 0)) (PreH5 : (target_same_priority <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = prio_same_priority)) (PreH11 : (srcTask_Prio_pre = prio_same_priority)) (PreH12 : (func_capability_pre = slot_same_priority)) (PreH13 : (rights_pre = requested_same_priority)) (PreH14 : (0 <= prio_same_priority)) (PreH15 : (prio_same_priority < 64)) (PreH16 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH17 : (0 <= slot_same_priority)) (PreH18 : (slot_same_priority <= 16)) (PreH19 : (target_same_priority <> 0)) (PreH20 : (0 <= requested_same_priority)) (PreH21 : (requested_same_priority <= UINT_MAX)) (PreH22 : (0 <= word1_same_priority)) (PreH23 : (word1_same_priority <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre old_kind_same_priority word0_same_priority word1_same_priority old_kind_same_priority word0_same_priority word1_same_priority old_kind_same_priority word0_same_priority word1_same_priority )
.

Definition ucos_CNode_Mint_return_wit_8_shared_cspace := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (old_kind_shared_cspace <> 1)) (PreH2 : (target_shared_cspace <> 0)) (PreH3 : (target_shared_cspace <> 0)) (PreH4 : (srcTask_Prio_pre < 64)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (func_capability_pre <= 16)) (PreH7 : (0 <= func_capability_pre)) (PreH8 : (destTask_Prio_pre = dest_shared_cspace)) (PreH9 : (srcTask_Prio_pre = src_shared_cspace)) (PreH10 : (func_capability_pre = slot_shared_cspace)) (PreH11 : (rights_pre = requested_shared_cspace)) (PreH12 : (0 <= dest_shared_cspace)) (PreH13 : (dest_shared_cspace < 64)) (PreH14 : (0 <= src_shared_cspace)) (PreH15 : (src_shared_cspace < 64)) (PreH16 : (dest_shared_cspace <> src_shared_cspace)) (PreH17 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH18 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH19 : (0 <= slot_shared_cspace)) (PreH20 : (slot_shared_cspace <= 16)) (PreH21 : (target_shared_cspace <> 0)) (PreH22 : (0 <= requested_shared_cspace)) (PreH23 : (requested_shared_cspace <= UINT_MAX)) (PreH24 : (0 <= word1_shared_cspace)) (PreH25 : (word1_shared_cspace <= UINT_MAX)) ,
  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (old_kind_shared_cspace <= UINT_MAX)) (PreH2 : (old_kind_shared_cspace >= 0)) (PreH3 : (old_kind_shared_cspace <> 1)) (PreH4 : (target_shared_cspace <> 0)) (PreH5 : (target_shared_cspace <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_shared_cspace)) (PreH11 : (srcTask_Prio_pre = src_shared_cspace)) (PreH12 : (func_capability_pre = slot_shared_cspace)) (PreH13 : (rights_pre = requested_shared_cspace)) (PreH14 : (0 <= dest_shared_cspace)) (PreH15 : (dest_shared_cspace < 64)) (PreH16 : (0 <= src_shared_cspace)) (PreH17 : (src_shared_cspace < 64)) (PreH18 : (dest_shared_cspace <> src_shared_cspace)) (PreH19 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH20 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH21 : (0 <= slot_shared_cspace)) (PreH22 : (slot_shared_cspace <= 16)) (PreH23 : (target_shared_cspace <> 0)) (PreH24 : (0 <= requested_shared_cspace)) (PreH25 : (requested_shared_cspace <= UINT_MAX)) (PreH26 : (0 <= word1_shared_cspace)) (PreH27 : (word1_shared_cspace <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre old_kind_shared_cspace word0_shared_cspace word1_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_8_shared_cspace_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (old_kind_shared_cspace <= UINT_MAX)) (PreH2 : (old_kind_shared_cspace >= 0)) (PreH3 : (old_kind_shared_cspace <> 1)) (PreH4 : (target_shared_cspace <> 0)) (PreH5 : (target_shared_cspace <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_shared_cspace)) (PreH11 : (srcTask_Prio_pre = src_shared_cspace)) (PreH12 : (func_capability_pre = slot_shared_cspace)) (PreH13 : (rights_pre = requested_shared_cspace)) (PreH14 : (0 <= dest_shared_cspace)) (PreH15 : (dest_shared_cspace < 64)) (PreH16 : (0 <= src_shared_cspace)) (PreH17 : (src_shared_cspace < 64)) (PreH18 : (dest_shared_cspace <> src_shared_cspace)) (PreH19 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH20 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH21 : (0 <= slot_shared_cspace)) (PreH22 : (slot_shared_cspace <= 16)) (PreH23 : (target_shared_cspace <> 0)) (PreH24 : (0 <= requested_shared_cspace)) (PreH25 : (requested_shared_cspace <= UINT_MAX)) (PreH26 : (0 <= word1_shared_cspace)) (PreH27 : (word1_shared_cspace <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre old_kind_shared_cspace word0_shared_cspace word1_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace )
.

Definition ucos_CNode_Mint_return_wit_9_distinct_cspaces := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <> 1)) (PreH2 : (source_distinct_cspaces <> 0)) (PreH3 : (target_distinct_cspaces <> 0)) (PreH4 : (srcTask_Prio_pre < 64)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (func_capability_pre <= 16)) (PreH7 : (0 <= func_capability_pre)) (PreH8 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH9 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH10 : (func_capability_pre = slot_distinct_cspaces)) (PreH11 : (rights_pre = requested_distinct_cspaces)) (PreH12 : (0 <= dest_distinct_cspaces)) (PreH13 : (dest_distinct_cspaces < 64)) (PreH14 : (0 <= src_distinct_cspaces)) (PreH15 : (src_distinct_cspaces < 64)) (PreH16 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH17 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH18 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH19 : (0 <= slot_distinct_cspaces)) (PreH20 : (slot_distinct_cspaces <= 16)) (PreH21 : (target_distinct_cspaces <> 0)) (PreH22 : (source_distinct_cspaces <> 0)) (PreH23 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH24 : (0 <= requested_distinct_cspaces)) (PreH25 : (requested_distinct_cspaces <= UINT_MAX)) (PreH26 : (0 <= src_word1_distinct_cspaces)) (PreH27 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_distinct_cspaces src_kind_distinct_cspaces src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <= UINT_MAX)) (PreH2 : (src_kind_distinct_cspaces >= 0)) (PreH3 : (src_kind_distinct_cspaces <> 1)) (PreH4 : (source_distinct_cspaces <> 0)) (PreH5 : (target_distinct_cspaces <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH11 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH12 : (func_capability_pre = slot_distinct_cspaces)) (PreH13 : (rights_pre = requested_distinct_cspaces)) (PreH14 : (0 <= dest_distinct_cspaces)) (PreH15 : (dest_distinct_cspaces < 64)) (PreH16 : (0 <= src_distinct_cspaces)) (PreH17 : (src_distinct_cspaces < 64)) (PreH18 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH20 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH21 : (0 <= slot_distinct_cspaces)) (PreH22 : (slot_distinct_cspaces <= 16)) (PreH23 : (target_distinct_cspaces <> 0)) (PreH24 : (source_distinct_cspaces <> 0)) (PreH25 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH26 : (0 <= requested_distinct_cspaces)) (PreH27 : (requested_distinct_cspaces <= UINT_MAX)) (PreH28 : (0 <= src_word1_distinct_cspaces)) (PreH29 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre src_kind_distinct_cspaces src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_9_distinct_cspaces_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <= UINT_MAX)) (PreH2 : (src_kind_distinct_cspaces >= 0)) (PreH3 : (src_kind_distinct_cspaces <> 1)) (PreH4 : (source_distinct_cspaces <> 0)) (PreH5 : (target_distinct_cspaces <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH11 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH12 : (func_capability_pre = slot_distinct_cspaces)) (PreH13 : (rights_pre = requested_distinct_cspaces)) (PreH14 : (0 <= dest_distinct_cspaces)) (PreH15 : (dest_distinct_cspaces < 64)) (PreH16 : (0 <= src_distinct_cspaces)) (PreH17 : (src_distinct_cspaces < 64)) (PreH18 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH20 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH21 : (0 <= slot_distinct_cspaces)) (PreH22 : (slot_distinct_cspaces <= 16)) (PreH23 : (target_distinct_cspaces <> 0)) (PreH24 : (source_distinct_cspaces <> 0)) (PreH25 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH26 : (0 <= requested_distinct_cspaces)) (PreH27 : (requested_distinct_cspaces <= UINT_MAX)) (PreH28 : (0 <= src_word1_distinct_cspaces)) (PreH29 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre src_kind_distinct_cspaces src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces )
.

Definition ucos_CNode_Mint_return_wit_10_distinct_cspaces := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_word1_distinct_cspaces = rights_pre)) (PreH2 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH3 : (src_kind_distinct_cspaces = 1)) (PreH4 : (source_distinct_cspaces <> 0)) (PreH5 : (target_distinct_cspaces <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH11 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH12 : (func_capability_pre = slot_distinct_cspaces)) (PreH13 : (rights_pre = requested_distinct_cspaces)) (PreH14 : (0 <= dest_distinct_cspaces)) (PreH15 : (dest_distinct_cspaces < 64)) (PreH16 : (0 <= src_distinct_cspaces)) (PreH17 : (src_distinct_cspaces < 64)) (PreH18 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH20 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH21 : (0 <= slot_distinct_cspaces)) (PreH22 : (slot_distinct_cspaces <= 16)) (PreH23 : (target_distinct_cspaces <> 0)) (PreH24 : (source_distinct_cspaces <> 0)) (PreH25 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH26 : (0 <= requested_distinct_cspaces)) (PreH27 : (requested_distinct_cspaces <= UINT_MAX)) (PreH28 : (0 <= src_word1_distinct_cspaces)) (PreH29 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_distinct_cspaces src_kind_distinct_cspaces src_word0_distinct_cspaces src_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <= UINT_MAX)) (PreH2 : (src_kind_distinct_cspaces >= 0)) (PreH3 : (src_word1_distinct_cspaces >= 0)) (PreH4 : (src_word1_distinct_cspaces = rights_pre)) (PreH5 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH6 : (src_kind_distinct_cspaces = 1)) (PreH7 : (source_distinct_cspaces <> 0)) (PreH8 : (target_distinct_cspaces <> 0)) (PreH9 : (srcTask_Prio_pre < 64)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (func_capability_pre <= 16)) (PreH12 : (0 <= func_capability_pre)) (PreH13 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH14 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH15 : (func_capability_pre = slot_distinct_cspaces)) (PreH16 : (rights_pre = requested_distinct_cspaces)) (PreH17 : (0 <= dest_distinct_cspaces)) (PreH18 : (dest_distinct_cspaces < 64)) (PreH19 : (0 <= src_distinct_cspaces)) (PreH20 : (src_distinct_cspaces < 64)) (PreH21 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH22 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH23 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH24 : (0 <= slot_distinct_cspaces)) (PreH25 : (slot_distinct_cspaces <= 16)) (PreH26 : (target_distinct_cspaces <> 0)) (PreH27 : (source_distinct_cspaces <> 0)) (PreH28 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH29 : (0 <= requested_distinct_cspaces)) (PreH30 : (requested_distinct_cspaces <= UINT_MAX)) (PreH31 : (0 <= src_word1_distinct_cspaces)) (PreH32 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre 1 src_word0_distinct_cspaces rights_pre dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_10_distinct_cspaces_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces <= UINT_MAX)) (PreH2 : (src_kind_distinct_cspaces >= 0)) (PreH3 : (src_word1_distinct_cspaces >= 0)) (PreH4 : (src_word1_distinct_cspaces = rights_pre)) (PreH5 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH6 : (src_kind_distinct_cspaces = 1)) (PreH7 : (source_distinct_cspaces <> 0)) (PreH8 : (target_distinct_cspaces <> 0)) (PreH9 : (srcTask_Prio_pre < 64)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (func_capability_pre <= 16)) (PreH12 : (0 <= func_capability_pre)) (PreH13 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH14 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH15 : (func_capability_pre = slot_distinct_cspaces)) (PreH16 : (rights_pre = requested_distinct_cspaces)) (PreH17 : (0 <= dest_distinct_cspaces)) (PreH18 : (dest_distinct_cspaces < 64)) (PreH19 : (0 <= src_distinct_cspaces)) (PreH20 : (src_distinct_cspaces < 64)) (PreH21 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH22 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH23 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH24 : (0 <= slot_distinct_cspaces)) (PreH25 : (slot_distinct_cspaces <= 16)) (PreH26 : (target_distinct_cspaces <> 0)) (PreH27 : (source_distinct_cspaces <> 0)) (PreH28 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH29 : (0 <= requested_distinct_cspaces)) (PreH30 : (requested_distinct_cspaces <= UINT_MAX)) (PreH31 : (0 <= src_word1_distinct_cspaces)) (PreH32 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre 1 src_word0_distinct_cspaces rights_pre dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces dst_kind_distinct_cspaces dst_word0_distinct_cspaces dst_word1_distinct_cspaces )
.

Definition ucos_CNode_Mint_return_wit_11_shared_cspace := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (word1_shared_cspace = rights_pre)) (PreH2 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) = 0)) (PreH3 : (old_kind_shared_cspace = 1)) (PreH4 : (target_shared_cspace <> 0)) (PreH5 : (target_shared_cspace <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_shared_cspace)) (PreH11 : (srcTask_Prio_pre = src_shared_cspace)) (PreH12 : (func_capability_pre = slot_shared_cspace)) (PreH13 : (rights_pre = requested_shared_cspace)) (PreH14 : (0 <= dest_shared_cspace)) (PreH15 : (dest_shared_cspace < 64)) (PreH16 : (0 <= src_shared_cspace)) (PreH17 : (src_shared_cspace < 64)) (PreH18 : (dest_shared_cspace <> src_shared_cspace)) (PreH19 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH20 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH21 : (0 <= slot_shared_cspace)) (PreH22 : (slot_shared_cspace <= 16)) (PreH23 : (target_shared_cspace <> 0)) (PreH24 : (0 <= requested_shared_cspace)) (PreH25 : (requested_shared_cspace <= UINT_MAX)) (PreH26 : (0 <= word1_shared_cspace)) (PreH27 : (word1_shared_cspace <= UINT_MAX)) ,
  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace old_kind_shared_cspace word0_shared_cspace word1_shared_cspace new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (old_kind_shared_cspace <= UINT_MAX)) (PreH2 : (old_kind_shared_cspace >= 0)) (PreH3 : (word1_shared_cspace >= 0)) (PreH4 : (word1_shared_cspace = rights_pre)) (PreH5 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) = 0)) (PreH6 : (old_kind_shared_cspace = 1)) (PreH7 : (target_shared_cspace <> 0)) (PreH8 : (target_shared_cspace <> 0)) (PreH9 : (srcTask_Prio_pre < 64)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (func_capability_pre <= 16)) (PreH12 : (0 <= func_capability_pre)) (PreH13 : (destTask_Prio_pre = dest_shared_cspace)) (PreH14 : (srcTask_Prio_pre = src_shared_cspace)) (PreH15 : (func_capability_pre = slot_shared_cspace)) (PreH16 : (rights_pre = requested_shared_cspace)) (PreH17 : (0 <= dest_shared_cspace)) (PreH18 : (dest_shared_cspace < 64)) (PreH19 : (0 <= src_shared_cspace)) (PreH20 : (src_shared_cspace < 64)) (PreH21 : (dest_shared_cspace <> src_shared_cspace)) (PreH22 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH23 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH24 : (0 <= slot_shared_cspace)) (PreH25 : (slot_shared_cspace <= 16)) (PreH26 : (target_shared_cspace <> 0)) (PreH27 : (0 <= requested_shared_cspace)) (PreH28 : (requested_shared_cspace <= UINT_MAX)) (PreH29 : (0 <= word1_shared_cspace)) (PreH30 : (word1_shared_cspace <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre 1 word0_shared_cspace rights_pre 1 word0_shared_cspace rights_pre 1 word0_shared_cspace rights_pre ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_11_shared_cspace_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (old_kind_shared_cspace <= UINT_MAX)) (PreH2 : (old_kind_shared_cspace >= 0)) (PreH3 : (word1_shared_cspace >= 0)) (PreH4 : (word1_shared_cspace = rights_pre)) (PreH5 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) = 0)) (PreH6 : (old_kind_shared_cspace = 1)) (PreH7 : (target_shared_cspace <> 0)) (PreH8 : (target_shared_cspace <> 0)) (PreH9 : (srcTask_Prio_pre < 64)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (func_capability_pre <= 16)) (PreH12 : (0 <= func_capability_pre)) (PreH13 : (destTask_Prio_pre = dest_shared_cspace)) (PreH14 : (srcTask_Prio_pre = src_shared_cspace)) (PreH15 : (func_capability_pre = slot_shared_cspace)) (PreH16 : (rights_pre = requested_shared_cspace)) (PreH17 : (0 <= dest_shared_cspace)) (PreH18 : (dest_shared_cspace < 64)) (PreH19 : (0 <= src_shared_cspace)) (PreH20 : (src_shared_cspace < 64)) (PreH21 : (dest_shared_cspace <> src_shared_cspace)) (PreH22 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH23 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH24 : (0 <= slot_shared_cspace)) (PreH25 : (slot_shared_cspace <= 16)) (PreH26 : (target_shared_cspace <> 0)) (PreH27 : (0 <= requested_shared_cspace)) (PreH28 : (requested_shared_cspace <= UINT_MAX)) (PreH29 : (0 <= word1_shared_cspace)) (PreH30 : (word1_shared_cspace <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre 1 word0_shared_cspace rights_pre 1 word0_shared_cspace rights_pre 1 word0_shared_cspace rights_pre )
.

Definition ucos_CNode_Mint_return_wit_12_same_priority := 
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (word1_same_priority = rights_pre)) (PreH2 : ((Z.land (Z.lnot word1_same_priority) rights_pre) = 0)) (PreH3 : (old_kind_same_priority = 1)) (PreH4 : (target_same_priority <> 0)) (PreH5 : (target_same_priority <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = prio_same_priority)) (PreH11 : (srcTask_Prio_pre = prio_same_priority)) (PreH12 : (func_capability_pre = slot_same_priority)) (PreH13 : (rights_pre = requested_same_priority)) (PreH14 : (0 <= prio_same_priority)) (PreH15 : (prio_same_priority < 64)) (PreH16 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH17 : (0 <= slot_same_priority)) (PreH18 : (slot_same_priority <= 16)) (PreH19 : (target_same_priority <> 0)) (PreH20 : (0 <= requested_same_priority)) (PreH21 : (requested_same_priority <= UINT_MAX)) (PreH22 : (0 <= word1_same_priority)) (PreH23 : (word1_same_priority <= UINT_MAX)) ,
  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
|--
  EX (new_kind: Z)  (new_word0: Z)  (new_word1: Z) ,
  “ (mint_cap_transition 5 requested_same_priority old_kind_same_priority word0_same_priority word1_same_priority old_kind_same_priority word0_same_priority word1_same_priority new_kind new_word0 new_word1 ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_kind)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_word0)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_word1)
) \/
(
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (old_kind_same_priority <= UINT_MAX)) (PreH2 : (old_kind_same_priority >= 0)) (PreH3 : (word1_same_priority >= 0)) (PreH4 : (word1_same_priority = rights_pre)) (PreH5 : ((Z.land (Z.lnot word1_same_priority) rights_pre) = 0)) (PreH6 : (old_kind_same_priority = 1)) (PreH7 : (target_same_priority <> 0)) (PreH8 : (target_same_priority <> 0)) (PreH9 : (srcTask_Prio_pre < 64)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (func_capability_pre <= 16)) (PreH12 : (0 <= func_capability_pre)) (PreH13 : (destTask_Prio_pre = prio_same_priority)) (PreH14 : (srcTask_Prio_pre = prio_same_priority)) (PreH15 : (func_capability_pre = slot_same_priority)) (PreH16 : (rights_pre = requested_same_priority)) (PreH17 : (0 <= prio_same_priority)) (PreH18 : (prio_same_priority < 64)) (PreH19 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH20 : (0 <= slot_same_priority)) (PreH21 : (slot_same_priority <= 16)) (PreH22 : (target_same_priority <> 0)) (PreH23 : (0 <= requested_same_priority)) (PreH24 : (requested_same_priority <= UINT_MAX)) (PreH25 : (0 <= word1_same_priority)) (PreH26 : (word1_same_priority <= UINT_MAX)) ,
  TT && emp 
|--
  “ (mint_cap_transition 5 rights_pre 1 word0_same_priority rights_pre 1 word0_same_priority rights_pre 1 word0_same_priority rights_pre ) ”
  &&  emp
).

Definition ucos_CNode_Mint_return_wit_12_same_priority_split_goal_1 := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (old_kind_same_priority <= UINT_MAX)) (PreH2 : (old_kind_same_priority >= 0)) (PreH3 : (word1_same_priority >= 0)) (PreH4 : (word1_same_priority = rights_pre)) (PreH5 : ((Z.land (Z.lnot word1_same_priority) rights_pre) = 0)) (PreH6 : (old_kind_same_priority = 1)) (PreH7 : (target_same_priority <> 0)) (PreH8 : (target_same_priority <> 0)) (PreH9 : (srcTask_Prio_pre < 64)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (func_capability_pre <= 16)) (PreH12 : (0 <= func_capability_pre)) (PreH13 : (destTask_Prio_pre = prio_same_priority)) (PreH14 : (srcTask_Prio_pre = prio_same_priority)) (PreH15 : (func_capability_pre = slot_same_priority)) (PreH16 : (rights_pre = requested_same_priority)) (PreH17 : (0 <= prio_same_priority)) (PreH18 : (prio_same_priority < 64)) (PreH19 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH20 : (0 <= slot_same_priority)) (PreH21 : (slot_same_priority <= 16)) (PreH22 : (target_same_priority <> 0)) (PreH23 : (0 <= requested_same_priority)) (PreH24 : (requested_same_priority <= UINT_MAX)) (PreH25 : (0 <= word1_same_priority)) (PreH26 : (word1_same_priority <= UINT_MAX)) ,
  (mint_cap_transition 5 rights_pre 1 word0_same_priority rights_pre 1 word0_same_priority rights_pre 1 word0_same_priority rights_pre )
.

Definition ucos_CNode_Mint_return_wit_13_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (target_null_distinct_priorities = 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH7 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH8 : (func_capability_pre = slot_null_distinct_priorities)) (PreH9 : (rights_pre = requested_null_distinct_priorities)) (PreH10 : (0 <= dest_null_distinct_priorities)) (PreH11 : (dest_null_distinct_priorities < 64)) (PreH12 : (0 <= src_null_distinct_priorities)) (PreH13 : (src_null_distinct_priorities < 64)) (PreH14 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH16 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH17 : (0 <= slot_null_distinct_priorities)) (PreH18 : (slot_null_distinct_priorities <= 16)) (PreH19 : (0 <= requested_null_distinct_priorities)) (PreH20 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH21 : (source_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
|--
  “ (5 = 5) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
.

Definition ucos_CNode_Mint_return_wit_14_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (target_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ (5 = 5) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
.

Definition ucos_CNode_Mint_return_wit_15_null_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_null_same_priority: Z) (slot_null_same_priority: Z) (prio_null_same_priority: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_null_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_null_same_priority)) (PreH7 : (func_capability_pre = slot_null_same_priority)) (PreH8 : (rights_pre = requested_null_same_priority)) (PreH9 : (0 <= prio_null_same_priority)) (PreH10 : (prio_null_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority)) (PreH12 : (0 <= slot_null_same_priority)) (PreH13 : (slot_null_same_priority <= 16)) (PreH14 : (0 <= requested_null_same_priority)) (PreH15 : (requested_null_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ (5 = 5) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (prio_null_same_priority * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_CNode_Mint_return_wit_16_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (target_null_distinct_priorities <> 0)) (PreH2 : (srcTask_Prio_pre < 64)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre <= 16)) (PreH5 : (0 <= func_capability_pre)) (PreH6 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH7 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH8 : (func_capability_pre = slot_null_distinct_priorities)) (PreH9 : (rights_pre = requested_null_distinct_priorities)) (PreH10 : (0 <= dest_null_distinct_priorities)) (PreH11 : (dest_null_distinct_priorities < 64)) (PreH12 : (0 <= src_null_distinct_priorities)) (PreH13 : (src_null_distinct_priorities < 64)) (PreH14 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH16 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH17 : (0 <= slot_null_distinct_priorities)) (PreH18 : (slot_null_distinct_priorities <= 16)) (PreH19 : (0 <= requested_null_distinct_priorities)) (PreH20 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH21 : (source_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
|--
  “ (5 = 5) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
.

Definition ucos_CNode_Mint_return_wit_17_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = dest_prio_invalid)) (PreH5 : (srcTask_Prio_pre = src_prio_invalid)) (PreH6 : (func_capability_pre = slot_prio_invalid)) (PreH7 : (rights_pre = requested_prio_invalid)) (PreH8 : (0 <= dest_prio_invalid)) (PreH9 : (dest_prio_invalid <= 255)) (PreH10 : (0 <= src_prio_invalid)) (PreH11 : (src_prio_invalid <= 255)) (PreH12 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH13 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH14 : (64 <= src_prio_invalid)) (PreH15 : (0 <= slot_prio_invalid)) (PreH16 : (slot_prio_invalid <= 16)) (PreH17 : (0 <= requested_prio_invalid)) (PreH18 : (requested_prio_invalid <= UINT_MAX)) ,
  TT && emp 
|--
  “ (5 = 5) ”
  &&  emp
.

Definition ucos_CNode_Mint_return_wit_18_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre <= 16)) (PreH3 : (0 <= func_capability_pre)) (PreH4 : (destTask_Prio_pre = dest_prio_invalid)) (PreH5 : (srcTask_Prio_pre = src_prio_invalid)) (PreH6 : (func_capability_pre = slot_prio_invalid)) (PreH7 : (rights_pre = requested_prio_invalid)) (PreH8 : (0 <= dest_prio_invalid)) (PreH9 : (dest_prio_invalid <= 255)) (PreH10 : (0 <= src_prio_invalid)) (PreH11 : (src_prio_invalid <= 255)) (PreH12 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH13 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH14 : (64 <= dest_prio_invalid)) (PreH15 : (0 <= slot_prio_invalid)) (PreH16 : (slot_prio_invalid <= 16)) (PreH17 : (0 <= requested_prio_invalid)) (PreH18 : (requested_prio_invalid <= UINT_MAX)) ,
  TT && emp 
|--
  “ (5 = 5) ”
  &&  emp
.

Definition ucos_CNode_Mint_return_wit_19_prio_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_prio_invalid: Z) (slot_prio_invalid: Z) (src_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (srcTask_Prio_pre >= 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_prio_invalid)) (PreH6 : (srcTask_Prio_pre = src_prio_invalid)) (PreH7 : (func_capability_pre = slot_prio_invalid)) (PreH8 : (rights_pre = requested_prio_invalid)) (PreH9 : (0 <= dest_prio_invalid)) (PreH10 : (dest_prio_invalid <= 255)) (PreH11 : (0 <= src_prio_invalid)) (PreH12 : (src_prio_invalid <= 255)) (PreH13 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH14 : ((unsigned_last_nbits (src_prio_invalid) (32)) = src_prio_invalid)) (PreH15 : (64 <= src_prio_invalid)) (PreH16 : (0 <= slot_prio_invalid)) (PreH17 : (slot_prio_invalid <= 16)) (PreH18 : (0 <= requested_prio_invalid)) (PreH19 : (requested_prio_invalid <= UINT_MAX)) ,
  TT && emp 
|--
  “ (5 = 5) ”
  &&  emp
.

Definition ucos_CNode_Mint_return_wit_20_class_invalid := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_class_invalid: Z) (slot_class_invalid: Z) (src_class_invalid: Z) (dest_class_invalid: Z) (PreH1 : (func_capability_pre > 16)) (PreH2 : (0 <= func_capability_pre)) (PreH3 : (destTask_Prio_pre = dest_class_invalid)) (PreH4 : (srcTask_Prio_pre = src_class_invalid)) (PreH5 : (func_capability_pre = slot_class_invalid)) (PreH6 : (rights_pre = requested_class_invalid)) (PreH7 : (0 <= dest_class_invalid)) (PreH8 : (dest_class_invalid <= 255)) (PreH9 : (0 <= src_class_invalid)) (PreH10 : (src_class_invalid <= 255)) (PreH11 : ((unsigned_last_nbits (dest_class_invalid) (32)) = dest_class_invalid)) (PreH12 : ((unsigned_last_nbits (src_class_invalid) (32)) = src_class_invalid)) (PreH13 : (16 < slot_class_invalid)) (PreH14 : (slot_class_invalid <= UINT_MAX)) (PreH15 : (0 <= requested_class_invalid)) (PreH16 : (requested_class_invalid <= UINT_MAX)) ,
  TT && emp 
|--
  “ (5 = 5) ”
  &&  emp
.

Definition ucos_CNode_Mint_partial_solve_wit_1_null_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_null_same_priority: Z) (slot_null_same_priority: Z) (prio_null_same_priority: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_null_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_null_same_priority)) (PreH7 : (func_capability_pre = slot_null_same_priority)) (PreH8 : (rights_pre = requested_null_same_priority)) (PreH9 : (0 <= prio_null_same_priority)) (PreH10 : (prio_null_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority)) (PreH12 : (0 <= slot_null_same_priority)) (PreH13 : (slot_null_same_priority <= 16)) (PreH14 : (0 <= requested_null_same_priority)) (PreH15 : (requested_null_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_null_same_priority * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = prio_null_same_priority) ” 
  &&  “ (srcTask_Prio_pre = prio_null_same_priority) ” 
  &&  “ (func_capability_pre = slot_null_same_priority) ” 
  &&  “ (rights_pre = requested_null_same_priority) ” 
  &&  “ (0 <= prio_null_same_priority) ” 
  &&  “ (prio_null_same_priority < 64) ” 
  &&  “ ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority) ” 
  &&  “ (0 <= slot_null_same_priority) ” 
  &&  “ (slot_null_same_priority <= 16) ” 
  &&  “ (0 <= requested_null_same_priority) ” 
  &&  “ (requested_null_same_priority <= UINT_MAX) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_CNode_Mint_partial_solve_wit_2_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (target_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_null_distinct_priorities) ” 
  &&  “ (srcTask_Prio_pre = src_null_distinct_priorities) ” 
  &&  “ (func_capability_pre = slot_null_distinct_priorities) ” 
  &&  “ (rights_pre = requested_null_distinct_priorities) ” 
  &&  “ (0 <= dest_null_distinct_priorities) ” 
  &&  “ (dest_null_distinct_priorities < 64) ” 
  &&  “ (0 <= src_null_distinct_priorities) ” 
  &&  “ (src_null_distinct_priorities < 64) ” 
  &&  “ (dest_null_distinct_priorities <> src_null_distinct_priorities) ” 
  &&  “ ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities) ” 
  &&  “ ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities) ” 
  &&  “ (0 <= slot_null_distinct_priorities) ” 
  &&  “ (slot_null_distinct_priorities <= 16) ” 
  &&  “ (0 <= requested_null_distinct_priorities) ” 
  &&  “ (requested_null_distinct_priorities <= UINT_MAX) ” 
  &&  “ (target_null_distinct_priorities = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
.

Definition ucos_CNode_Mint_partial_solve_wit_3_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (source_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_null_distinct_priorities) ” 
  &&  “ (srcTask_Prio_pre = src_null_distinct_priorities) ” 
  &&  “ (func_capability_pre = slot_null_distinct_priorities) ” 
  &&  “ (rights_pre = requested_null_distinct_priorities) ” 
  &&  “ (0 <= dest_null_distinct_priorities) ” 
  &&  “ (dest_null_distinct_priorities < 64) ” 
  &&  “ (0 <= src_null_distinct_priorities) ” 
  &&  “ (src_null_distinct_priorities < 64) ” 
  &&  “ (dest_null_distinct_priorities <> src_null_distinct_priorities) ” 
  &&  “ ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities) ” 
  &&  “ ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities) ” 
  &&  “ (0 <= slot_null_distinct_priorities) ” 
  &&  “ (slot_null_distinct_priorities <= 16) ” 
  &&  “ (0 <= requested_null_distinct_priorities) ” 
  &&  “ (requested_null_distinct_priorities <= UINT_MAX) ” 
  &&  “ (source_null_distinct_priorities = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
.

Definition ucos_CNode_Mint_partial_solve_wit_4_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_same_priority)) (PreH7 : (func_capability_pre = slot_same_priority)) (PreH8 : (rights_pre = requested_same_priority)) (PreH9 : (0 <= prio_same_priority)) (PreH10 : (prio_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH12 : (0 <= slot_same_priority)) (PreH13 : (slot_same_priority <= 16)) (PreH14 : (target_same_priority <> 0)) (PreH15 : (0 <= requested_same_priority)) (PreH16 : (requested_same_priority <= UINT_MAX)) (PreH17 : (0 <= word1_same_priority)) (PreH18 : (word1_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (prio_same_priority * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = prio_same_priority) ” 
  &&  “ (srcTask_Prio_pre = prio_same_priority) ” 
  &&  “ (func_capability_pre = slot_same_priority) ” 
  &&  “ (rights_pre = requested_same_priority) ” 
  &&  “ (0 <= prio_same_priority) ” 
  &&  “ (prio_same_priority < 64) ” 
  &&  “ ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority) ” 
  &&  “ (0 <= slot_same_priority) ” 
  &&  “ (slot_same_priority <= 16) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (0 <= requested_same_priority) ” 
  &&  “ (requested_same_priority <= UINT_MAX) ” 
  &&  “ (0 <= word1_same_priority) ” 
  &&  “ (word1_same_priority <= UINT_MAX) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
.

Definition ucos_CNode_Mint_partial_solve_wit_5_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_shared_cspace)) (PreH6 : (srcTask_Prio_pre = src_shared_cspace)) (PreH7 : (func_capability_pre = slot_shared_cspace)) (PreH8 : (rights_pre = requested_shared_cspace)) (PreH9 : (0 <= dest_shared_cspace)) (PreH10 : (dest_shared_cspace < 64)) (PreH11 : (0 <= src_shared_cspace)) (PreH12 : (src_shared_cspace < 64)) (PreH13 : (dest_shared_cspace <> src_shared_cspace)) (PreH14 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH15 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH16 : (0 <= slot_shared_cspace)) (PreH17 : (slot_shared_cspace <= 16)) (PreH18 : (target_shared_cspace <> 0)) (PreH19 : (0 <= requested_shared_cspace)) (PreH20 : (requested_shared_cspace <= UINT_MAX)) (PreH21 : (0 <= word1_shared_cspace)) (PreH22 : (word1_shared_cspace <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_shared_cspace) ” 
  &&  “ (srcTask_Prio_pre = src_shared_cspace) ” 
  &&  “ (func_capability_pre = slot_shared_cspace) ” 
  &&  “ (rights_pre = requested_shared_cspace) ” 
  &&  “ (0 <= dest_shared_cspace) ” 
  &&  “ (dest_shared_cspace < 64) ” 
  &&  “ (0 <= src_shared_cspace) ” 
  &&  “ (src_shared_cspace < 64) ” 
  &&  “ (dest_shared_cspace <> src_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace) ” 
  &&  “ (0 <= slot_shared_cspace) ” 
  &&  “ (slot_shared_cspace <= 16) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (0 <= requested_shared_cspace) ” 
  &&  “ (requested_shared_cspace <= UINT_MAX) ” 
  &&  “ (0 <= word1_shared_cspace) ” 
  &&  “ (word1_shared_cspace <= UINT_MAX) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
.

Definition ucos_CNode_Mint_partial_solve_wit_6_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH6 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH7 : (func_capability_pre = slot_distinct_cspaces)) (PreH8 : (rights_pre = requested_distinct_cspaces)) (PreH9 : (0 <= dest_distinct_cspaces)) (PreH10 : (dest_distinct_cspaces < 64)) (PreH11 : (0 <= src_distinct_cspaces)) (PreH12 : (src_distinct_cspaces < 64)) (PreH13 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH14 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH15 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH16 : (0 <= slot_distinct_cspaces)) (PreH17 : (slot_distinct_cspaces <= 16)) (PreH18 : (target_distinct_cspaces <> 0)) (PreH19 : (source_distinct_cspaces <> 0)) (PreH20 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH21 : (0 <= requested_distinct_cspaces)) (PreH22 : (requested_distinct_cspaces <= UINT_MAX)) (PreH23 : (0 <= src_word1_distinct_cspaces)) (PreH24 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_distinct_cspaces) ” 
  &&  “ (srcTask_Prio_pre = src_distinct_cspaces) ” 
  &&  “ (func_capability_pre = slot_distinct_cspaces) ” 
  &&  “ (rights_pre = requested_distinct_cspaces) ” 
  &&  “ (0 <= dest_distinct_cspaces) ” 
  &&  “ (dest_distinct_cspaces < 64) ” 
  &&  “ (0 <= src_distinct_cspaces) ” 
  &&  “ (src_distinct_cspaces < 64) ” 
  &&  “ (dest_distinct_cspaces <> src_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces) ” 
  &&  “ (0 <= slot_distinct_cspaces) ” 
  &&  “ (slot_distinct_cspaces <= 16) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> source_distinct_cspaces) ” 
  &&  “ (0 <= requested_distinct_cspaces) ” 
  &&  “ (requested_distinct_cspaces <= UINT_MAX) ” 
  &&  “ (0 <= src_word1_distinct_cspaces) ” 
  &&  “ (src_word1_distinct_cspaces <= UINT_MAX) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
.

Definition ucos_CNode_Mint_partial_solve_wit_7_null_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (requested_null_same_priority: Z) (slot_null_same_priority: Z) (prio_null_same_priority: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_null_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_null_same_priority)) (PreH7 : (func_capability_pre = slot_null_same_priority)) (PreH8 : (rights_pre = requested_null_same_priority)) (PreH9 : (0 <= prio_null_same_priority)) (PreH10 : (prio_null_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority)) (PreH12 : (0 <= slot_null_same_priority)) (PreH13 : (slot_null_same_priority <= 16)) (PreH14 : (0 <= requested_null_same_priority)) (PreH15 : (requested_null_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = prio_null_same_priority) ” 
  &&  “ (srcTask_Prio_pre = prio_null_same_priority) ” 
  &&  “ (func_capability_pre = slot_null_same_priority) ” 
  &&  “ (rights_pre = requested_null_same_priority) ” 
  &&  “ (0 <= prio_null_same_priority) ” 
  &&  “ (prio_null_same_priority < 64) ” 
  &&  “ ((unsigned_last_nbits (prio_null_same_priority) (32)) = prio_null_same_priority) ” 
  &&  “ (0 <= slot_null_same_priority) ” 
  &&  “ (slot_null_same_priority <= 16) ” 
  &&  “ (0 <= requested_null_same_priority) ” 
  &&  “ (requested_null_same_priority <= UINT_MAX) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_CNode_Mint_partial_solve_wit_8_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (target_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_null_distinct_priorities) ” 
  &&  “ (srcTask_Prio_pre = src_null_distinct_priorities) ” 
  &&  “ (func_capability_pre = slot_null_distinct_priorities) ” 
  &&  “ (rights_pre = requested_null_distinct_priorities) ” 
  &&  “ (0 <= dest_null_distinct_priorities) ” 
  &&  “ (dest_null_distinct_priorities < 64) ” 
  &&  “ (0 <= src_null_distinct_priorities) ” 
  &&  “ (src_null_distinct_priorities < 64) ” 
  &&  “ (dest_null_distinct_priorities <> src_null_distinct_priorities) ” 
  &&  “ ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities) ” 
  &&  “ ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities) ” 
  &&  “ (0 <= slot_null_distinct_priorities) ” 
  &&  “ (slot_null_distinct_priorities <= 16) ” 
  &&  “ (0 <= requested_null_distinct_priorities) ” 
  &&  “ (requested_null_distinct_priorities <= UINT_MAX) ” 
  &&  “ (target_null_distinct_priorities = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_CNode_Mint_partial_solve_wit_9_null_distinct_priorities := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (source_null_distinct_priorities: Z) (target_null_distinct_priorities: Z) (requested_null_distinct_priorities: Z) (slot_null_distinct_priorities: Z) (src_null_distinct_priorities: Z) (dest_null_distinct_priorities: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_null_distinct_priorities)) (PreH6 : (srcTask_Prio_pre = src_null_distinct_priorities)) (PreH7 : (func_capability_pre = slot_null_distinct_priorities)) (PreH8 : (rights_pre = requested_null_distinct_priorities)) (PreH9 : (0 <= dest_null_distinct_priorities)) (PreH10 : (dest_null_distinct_priorities < 64)) (PreH11 : (0 <= src_null_distinct_priorities)) (PreH12 : (src_null_distinct_priorities < 64)) (PreH13 : (dest_null_distinct_priorities <> src_null_distinct_priorities)) (PreH14 : ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities)) (PreH15 : ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities)) (PreH16 : (0 <= slot_null_distinct_priorities)) (PreH17 : (slot_null_distinct_priorities <= 16)) (PreH18 : (0 <= requested_null_distinct_priorities)) (PreH19 : (requested_null_distinct_priorities <= UINT_MAX)) (PreH20 : (source_null_distinct_priorities = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_null_distinct_priorities * sizeof(PTR)))) # Ptr  |-> source_null_distinct_priorities)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_null_distinct_priorities) ” 
  &&  “ (srcTask_Prio_pre = src_null_distinct_priorities) ” 
  &&  “ (func_capability_pre = slot_null_distinct_priorities) ” 
  &&  “ (rights_pre = requested_null_distinct_priorities) ” 
  &&  “ (0 <= dest_null_distinct_priorities) ” 
  &&  “ (dest_null_distinct_priorities < 64) ” 
  &&  “ (0 <= src_null_distinct_priorities) ” 
  &&  “ (src_null_distinct_priorities < 64) ” 
  &&  “ (dest_null_distinct_priorities <> src_null_distinct_priorities) ” 
  &&  “ ((unsigned_last_nbits (dest_null_distinct_priorities) (32)) = dest_null_distinct_priorities) ” 
  &&  “ ((unsigned_last_nbits (src_null_distinct_priorities) (32)) = src_null_distinct_priorities) ” 
  &&  “ (0 <= slot_null_distinct_priorities) ” 
  &&  “ (slot_null_distinct_priorities <= 16) ” 
  &&  “ (0 <= requested_null_distinct_priorities) ” 
  &&  “ (requested_null_distinct_priorities <= UINT_MAX) ” 
  &&  “ (source_null_distinct_priorities = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_null_distinct_priorities)
.

Definition ucos_CNode_Mint_partial_solve_wit_10_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = prio_same_priority)) (PreH6 : (srcTask_Prio_pre = prio_same_priority)) (PreH7 : (func_capability_pre = slot_same_priority)) (PreH8 : (rights_pre = requested_same_priority)) (PreH9 : (0 <= prio_same_priority)) (PreH10 : (prio_same_priority < 64)) (PreH11 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH12 : (0 <= slot_same_priority)) (PreH13 : (slot_same_priority <= 16)) (PreH14 : (target_same_priority <> 0)) (PreH15 : (0 <= requested_same_priority)) (PreH16 : (requested_same_priority <= UINT_MAX)) (PreH17 : (0 <= word1_same_priority)) (PreH18 : (word1_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = prio_same_priority) ” 
  &&  “ (srcTask_Prio_pre = prio_same_priority) ” 
  &&  “ (func_capability_pre = slot_same_priority) ” 
  &&  “ (rights_pre = requested_same_priority) ” 
  &&  “ (0 <= prio_same_priority) ” 
  &&  “ (prio_same_priority < 64) ” 
  &&  “ ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority) ” 
  &&  “ (0 <= slot_same_priority) ” 
  &&  “ (slot_same_priority <= 16) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (0 <= requested_same_priority) ” 
  &&  “ (requested_same_priority <= UINT_MAX) ” 
  &&  “ (0 <= word1_same_priority) ” 
  &&  “ (word1_same_priority <= UINT_MAX) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
.

Definition ucos_CNode_Mint_partial_solve_wit_11_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_shared_cspace)) (PreH6 : (srcTask_Prio_pre = src_shared_cspace)) (PreH7 : (func_capability_pre = slot_shared_cspace)) (PreH8 : (rights_pre = requested_shared_cspace)) (PreH9 : (0 <= dest_shared_cspace)) (PreH10 : (dest_shared_cspace < 64)) (PreH11 : (0 <= src_shared_cspace)) (PreH12 : (src_shared_cspace < 64)) (PreH13 : (dest_shared_cspace <> src_shared_cspace)) (PreH14 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH15 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH16 : (0 <= slot_shared_cspace)) (PreH17 : (slot_shared_cspace <= 16)) (PreH18 : (target_shared_cspace <> 0)) (PreH19 : (0 <= requested_shared_cspace)) (PreH20 : (requested_shared_cspace <= UINT_MAX)) (PreH21 : (0 <= word1_shared_cspace)) (PreH22 : (word1_shared_cspace <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_shared_cspace * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_shared_cspace) ” 
  &&  “ (srcTask_Prio_pre = src_shared_cspace) ” 
  &&  “ (func_capability_pre = slot_shared_cspace) ” 
  &&  “ (rights_pre = requested_shared_cspace) ” 
  &&  “ (0 <= dest_shared_cspace) ” 
  &&  “ (dest_shared_cspace < 64) ” 
  &&  “ (0 <= src_shared_cspace) ” 
  &&  “ (src_shared_cspace < 64) ” 
  &&  “ (dest_shared_cspace <> src_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace) ” 
  &&  “ (0 <= slot_shared_cspace) ” 
  &&  “ (slot_shared_cspace <= 16) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (0 <= requested_shared_cspace) ” 
  &&  “ (requested_shared_cspace <= UINT_MAX) ” 
  &&  “ (0 <= word1_shared_cspace) ” 
  &&  “ (word1_shared_cspace <= UINT_MAX) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
.

Definition ucos_CNode_Mint_partial_solve_wit_12_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (srcTask_Prio_pre < 64)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre <= 16)) (PreH4 : (0 <= func_capability_pre)) (PreH5 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH6 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH7 : (func_capability_pre = slot_distinct_cspaces)) (PreH8 : (rights_pre = requested_distinct_cspaces)) (PreH9 : (0 <= dest_distinct_cspaces)) (PreH10 : (dest_distinct_cspaces < 64)) (PreH11 : (0 <= src_distinct_cspaces)) (PreH12 : (src_distinct_cspaces < 64)) (PreH13 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH14 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH15 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH16 : (0 <= slot_distinct_cspaces)) (PreH17 : (slot_distinct_cspaces <= 16)) (PreH18 : (target_distinct_cspaces <> 0)) (PreH19 : (source_distinct_cspaces <> 0)) (PreH20 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH21 : (0 <= requested_distinct_cspaces)) (PreH22 : (requested_distinct_cspaces <= UINT_MAX)) (PreH23 : (0 <= src_word1_distinct_cspaces)) (PreH24 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (src_distinct_cspaces * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_distinct_cspaces) ” 
  &&  “ (srcTask_Prio_pre = src_distinct_cspaces) ” 
  &&  “ (func_capability_pre = slot_distinct_cspaces) ” 
  &&  “ (rights_pre = requested_distinct_cspaces) ” 
  &&  “ (0 <= dest_distinct_cspaces) ” 
  &&  “ (dest_distinct_cspaces < 64) ” 
  &&  “ (0 <= src_distinct_cspaces) ” 
  &&  “ (src_distinct_cspaces < 64) ” 
  &&  “ (dest_distinct_cspaces <> src_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces) ” 
  &&  “ (0 <= slot_distinct_cspaces) ” 
  &&  “ (slot_distinct_cspaces <= 16) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> source_distinct_cspaces) ” 
  &&  “ (0 <= requested_distinct_cspaces) ” 
  &&  “ (requested_distinct_cspaces <= UINT_MAX) ” 
  &&  “ (0 <= src_word1_distinct_cspaces) ” 
  &&  “ (src_word1_distinct_cspaces <= UINT_MAX) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
.

Definition ucos_CNode_Mint_partial_solve_wit_13_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (target_same_priority <> 0)) (PreH2 : (target_same_priority <> 0)) (PreH3 : (srcTask_Prio_pre < 64)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre <= 16)) (PreH6 : (0 <= func_capability_pre)) (PreH7 : (destTask_Prio_pre = prio_same_priority)) (PreH8 : (srcTask_Prio_pre = prio_same_priority)) (PreH9 : (func_capability_pre = slot_same_priority)) (PreH10 : (rights_pre = requested_same_priority)) (PreH11 : (0 <= prio_same_priority)) (PreH12 : (prio_same_priority < 64)) (PreH13 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH14 : (0 <= slot_same_priority)) (PreH15 : (slot_same_priority <= 16)) (PreH16 : (target_same_priority <> 0)) (PreH17 : (0 <= requested_same_priority)) (PreH18 : (requested_same_priority <= UINT_MAX)) (PreH19 : (0 <= word1_same_priority)) (PreH20 : (word1_same_priority <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ (target_same_priority <> 0) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = prio_same_priority) ” 
  &&  “ (srcTask_Prio_pre = prio_same_priority) ” 
  &&  “ (func_capability_pre = slot_same_priority) ” 
  &&  “ (rights_pre = requested_same_priority) ” 
  &&  “ (0 <= prio_same_priority) ” 
  &&  “ (prio_same_priority < 64) ” 
  &&  “ ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority) ” 
  &&  “ (0 <= slot_same_priority) ” 
  &&  “ (slot_same_priority <= 16) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (0 <= requested_same_priority) ” 
  &&  “ (requested_same_priority <= UINT_MAX) ” 
  &&  “ (0 <= word1_same_priority) ” 
  &&  “ (word1_same_priority <= UINT_MAX) ”
  &&  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
.

Definition ucos_CNode_Mint_partial_solve_wit_14_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (target_shared_cspace <> 0)) (PreH2 : (target_shared_cspace <> 0)) (PreH3 : (srcTask_Prio_pre < 64)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre <= 16)) (PreH6 : (0 <= func_capability_pre)) (PreH7 : (destTask_Prio_pre = dest_shared_cspace)) (PreH8 : (srcTask_Prio_pre = src_shared_cspace)) (PreH9 : (func_capability_pre = slot_shared_cspace)) (PreH10 : (rights_pre = requested_shared_cspace)) (PreH11 : (0 <= dest_shared_cspace)) (PreH12 : (dest_shared_cspace < 64)) (PreH13 : (0 <= src_shared_cspace)) (PreH14 : (src_shared_cspace < 64)) (PreH15 : (dest_shared_cspace <> src_shared_cspace)) (PreH16 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH17 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH18 : (0 <= slot_shared_cspace)) (PreH19 : (slot_shared_cspace <= 16)) (PreH20 : (target_shared_cspace <> 0)) (PreH21 : (0 <= requested_shared_cspace)) (PreH22 : (requested_shared_cspace <= UINT_MAX)) (PreH23 : (0 <= word1_shared_cspace)) (PreH24 : (word1_shared_cspace <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ (target_shared_cspace <> 0) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_shared_cspace) ” 
  &&  “ (srcTask_Prio_pre = src_shared_cspace) ” 
  &&  “ (func_capability_pre = slot_shared_cspace) ” 
  &&  “ (rights_pre = requested_shared_cspace) ” 
  &&  “ (0 <= dest_shared_cspace) ” 
  &&  “ (dest_shared_cspace < 64) ” 
  &&  “ (0 <= src_shared_cspace) ” 
  &&  “ (src_shared_cspace < 64) ” 
  &&  “ (dest_shared_cspace <> src_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace) ” 
  &&  “ (0 <= slot_shared_cspace) ” 
  &&  “ (slot_shared_cspace <= 16) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (0 <= requested_shared_cspace) ” 
  &&  “ (requested_shared_cspace <= UINT_MAX) ” 
  &&  “ (0 <= word1_shared_cspace) ” 
  &&  “ (word1_shared_cspace <= UINT_MAX) ”
  &&  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
.

Definition ucos_CNode_Mint_partial_solve_wit_15_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (source_distinct_cspaces <> 0)) (PreH2 : (target_distinct_cspaces <> 0)) (PreH3 : (srcTask_Prio_pre < 64)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre <= 16)) (PreH6 : (0 <= func_capability_pre)) (PreH7 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH8 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH9 : (func_capability_pre = slot_distinct_cspaces)) (PreH10 : (rights_pre = requested_distinct_cspaces)) (PreH11 : (0 <= dest_distinct_cspaces)) (PreH12 : (dest_distinct_cspaces < 64)) (PreH13 : (0 <= src_distinct_cspaces)) (PreH14 : (src_distinct_cspaces < 64)) (PreH15 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH16 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH17 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH18 : (0 <= slot_distinct_cspaces)) (PreH19 : (slot_distinct_cspaces <= 16)) (PreH20 : (target_distinct_cspaces <> 0)) (PreH21 : (source_distinct_cspaces <> 0)) (PreH22 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH23 : (0 <= requested_distinct_cspaces)) (PreH24 : (requested_distinct_cspaces <= UINT_MAX)) (PreH25 : (0 <= src_word1_distinct_cspaces)) (PreH26 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_distinct_cspaces) ” 
  &&  “ (srcTask_Prio_pre = src_distinct_cspaces) ” 
  &&  “ (func_capability_pre = slot_distinct_cspaces) ” 
  &&  “ (rights_pre = requested_distinct_cspaces) ” 
  &&  “ (0 <= dest_distinct_cspaces) ” 
  &&  “ (dest_distinct_cspaces < 64) ” 
  &&  “ (0 <= src_distinct_cspaces) ” 
  &&  “ (src_distinct_cspaces < 64) ” 
  &&  “ (dest_distinct_cspaces <> src_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces) ” 
  &&  “ (0 <= slot_distinct_cspaces) ” 
  &&  “ (slot_distinct_cspaces <= 16) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> source_distinct_cspaces) ” 
  &&  “ (0 <= requested_distinct_cspaces) ” 
  &&  “ (requested_distinct_cspaces <= UINT_MAX) ” 
  &&  “ (0 <= src_word1_distinct_cspaces) ” 
  &&  “ (src_word1_distinct_cspaces <= UINT_MAX) ”
  &&  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
.

Definition ucos_CNode_Mint_partial_solve_wit_16_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_kind_distinct_cspaces = 1)) (PreH2 : (source_distinct_cspaces <> 0)) (PreH3 : (target_distinct_cspaces <> 0)) (PreH4 : (srcTask_Prio_pre < 64)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (func_capability_pre <= 16)) (PreH7 : (0 <= func_capability_pre)) (PreH8 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH9 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH10 : (func_capability_pre = slot_distinct_cspaces)) (PreH11 : (rights_pre = requested_distinct_cspaces)) (PreH12 : (0 <= dest_distinct_cspaces)) (PreH13 : (dest_distinct_cspaces < 64)) (PreH14 : (0 <= src_distinct_cspaces)) (PreH15 : (src_distinct_cspaces < 64)) (PreH16 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH17 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH18 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH19 : (0 <= slot_distinct_cspaces)) (PreH20 : (slot_distinct_cspaces <= 16)) (PreH21 : (target_distinct_cspaces <> 0)) (PreH22 : (source_distinct_cspaces <> 0)) (PreH23 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH24 : (0 <= requested_distinct_cspaces)) (PreH25 : (requested_distinct_cspaces <= UINT_MAX)) (PreH26 : (0 <= src_word1_distinct_cspaces)) (PreH27 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (src_kind_distinct_cspaces = 1) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_distinct_cspaces) ” 
  &&  “ (srcTask_Prio_pre = src_distinct_cspaces) ” 
  &&  “ (func_capability_pre = slot_distinct_cspaces) ” 
  &&  “ (rights_pre = requested_distinct_cspaces) ” 
  &&  “ (0 <= dest_distinct_cspaces) ” 
  &&  “ (dest_distinct_cspaces < 64) ” 
  &&  “ (0 <= src_distinct_cspaces) ” 
  &&  “ (src_distinct_cspaces < 64) ” 
  &&  “ (dest_distinct_cspaces <> src_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces) ” 
  &&  “ (0 <= slot_distinct_cspaces) ” 
  &&  “ (slot_distinct_cspaces <= 16) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> source_distinct_cspaces) ” 
  &&  “ (0 <= requested_distinct_cspaces) ” 
  &&  “ (requested_distinct_cspaces <= UINT_MAX) ” 
  &&  “ (0 <= src_word1_distinct_cspaces) ” 
  &&  “ (src_word1_distinct_cspaces <= UINT_MAX) ”
  &&  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
.

Definition ucos_CNode_Mint_partial_solve_wit_17_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (old_kind_shared_cspace = 1)) (PreH2 : (target_shared_cspace <> 0)) (PreH3 : (target_shared_cspace <> 0)) (PreH4 : (srcTask_Prio_pre < 64)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (func_capability_pre <= 16)) (PreH7 : (0 <= func_capability_pre)) (PreH8 : (destTask_Prio_pre = dest_shared_cspace)) (PreH9 : (srcTask_Prio_pre = src_shared_cspace)) (PreH10 : (func_capability_pre = slot_shared_cspace)) (PreH11 : (rights_pre = requested_shared_cspace)) (PreH12 : (0 <= dest_shared_cspace)) (PreH13 : (dest_shared_cspace < 64)) (PreH14 : (0 <= src_shared_cspace)) (PreH15 : (src_shared_cspace < 64)) (PreH16 : (dest_shared_cspace <> src_shared_cspace)) (PreH17 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH18 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH19 : (0 <= slot_shared_cspace)) (PreH20 : (slot_shared_cspace <= 16)) (PreH21 : (target_shared_cspace <> 0)) (PreH22 : (0 <= requested_shared_cspace)) (PreH23 : (requested_shared_cspace <= UINT_MAX)) (PreH24 : (0 <= word1_shared_cspace)) (PreH25 : (word1_shared_cspace <= UINT_MAX)) ,
  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
|--
  “ (old_kind_shared_cspace = 1) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_shared_cspace) ” 
  &&  “ (srcTask_Prio_pre = src_shared_cspace) ” 
  &&  “ (func_capability_pre = slot_shared_cspace) ” 
  &&  “ (rights_pre = requested_shared_cspace) ” 
  &&  “ (0 <= dest_shared_cspace) ” 
  &&  “ (dest_shared_cspace < 64) ” 
  &&  “ (0 <= src_shared_cspace) ” 
  &&  “ (src_shared_cspace < 64) ” 
  &&  “ (dest_shared_cspace <> src_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace) ” 
  &&  “ (0 <= slot_shared_cspace) ” 
  &&  “ (slot_shared_cspace <= 16) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (0 <= requested_shared_cspace) ” 
  &&  “ (requested_shared_cspace <= UINT_MAX) ” 
  &&  “ (0 <= word1_shared_cspace) ” 
  &&  “ (word1_shared_cspace <= UINT_MAX) ”
  &&  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
.

Definition ucos_CNode_Mint_partial_solve_wit_18_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (old_kind_same_priority = 1)) (PreH2 : (target_same_priority <> 0)) (PreH3 : (target_same_priority <> 0)) (PreH4 : (srcTask_Prio_pre < 64)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (func_capability_pre <= 16)) (PreH7 : (0 <= func_capability_pre)) (PreH8 : (destTask_Prio_pre = prio_same_priority)) (PreH9 : (srcTask_Prio_pre = prio_same_priority)) (PreH10 : (func_capability_pre = slot_same_priority)) (PreH11 : (rights_pre = requested_same_priority)) (PreH12 : (0 <= prio_same_priority)) (PreH13 : (prio_same_priority < 64)) (PreH14 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH15 : (0 <= slot_same_priority)) (PreH16 : (slot_same_priority <= 16)) (PreH17 : (target_same_priority <> 0)) (PreH18 : (0 <= requested_same_priority)) (PreH19 : (requested_same_priority <= UINT_MAX)) (PreH20 : (0 <= word1_same_priority)) (PreH21 : (word1_same_priority <= UINT_MAX)) ,
  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
|--
  “ (old_kind_same_priority = 1) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = prio_same_priority) ” 
  &&  “ (srcTask_Prio_pre = prio_same_priority) ” 
  &&  “ (func_capability_pre = slot_same_priority) ” 
  &&  “ (rights_pre = requested_same_priority) ” 
  &&  “ (0 <= prio_same_priority) ” 
  &&  “ (prio_same_priority < 64) ” 
  &&  “ ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority) ” 
  &&  “ (0 <= slot_same_priority) ” 
  &&  “ (slot_same_priority <= 16) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (0 <= requested_same_priority) ” 
  &&  “ (requested_same_priority <= UINT_MAX) ” 
  &&  “ (0 <= word1_same_priority) ” 
  &&  “ (word1_same_priority <= UINT_MAX) ”
  &&  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_kind_same_priority)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
.

Definition ucos_CNode_Mint_partial_solve_wit_19_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (dst_kind_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_word1_distinct_cspaces <> rights_pre)) (PreH2 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH3 : (src_kind_distinct_cspaces = 1)) (PreH4 : (source_distinct_cspaces <> 0)) (PreH5 : (target_distinct_cspaces <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH11 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH12 : (func_capability_pre = slot_distinct_cspaces)) (PreH13 : (rights_pre = requested_distinct_cspaces)) (PreH14 : (0 <= dest_distinct_cspaces)) (PreH15 : (dest_distinct_cspaces < 64)) (PreH16 : (0 <= src_distinct_cspaces)) (PreH17 : (src_distinct_cspaces < 64)) (PreH18 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH20 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH21 : (0 <= slot_distinct_cspaces)) (PreH22 : (slot_distinct_cspaces <= 16)) (PreH23 : (target_distinct_cspaces <> 0)) (PreH24 : (source_distinct_cspaces <> 0)) (PreH25 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH26 : (0 <= requested_distinct_cspaces)) (PreH27 : (requested_distinct_cspaces <= UINT_MAX)) (PreH28 : (0 <= src_word1_distinct_cspaces)) (PreH29 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> dst_kind_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (src_word1_distinct_cspaces <> rights_pre) ” 
  &&  “ ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0) ” 
  &&  “ (src_kind_distinct_cspaces = 1) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_distinct_cspaces) ” 
  &&  “ (srcTask_Prio_pre = src_distinct_cspaces) ” 
  &&  “ (func_capability_pre = slot_distinct_cspaces) ” 
  &&  “ (rights_pre = requested_distinct_cspaces) ” 
  &&  “ (0 <= dest_distinct_cspaces) ” 
  &&  “ (dest_distinct_cspaces < 64) ” 
  &&  “ (0 <= src_distinct_cspaces) ” 
  &&  “ (src_distinct_cspaces < 64) ” 
  &&  “ (dest_distinct_cspaces <> src_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces) ” 
  &&  “ (0 <= slot_distinct_cspaces) ” 
  &&  “ (slot_distinct_cspaces <= 16) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> source_distinct_cspaces) ” 
  &&  “ (0 <= requested_distinct_cspaces) ” 
  &&  “ (requested_distinct_cspaces <= UINT_MAX) ” 
  &&  “ (0 <= src_word1_distinct_cspaces) ” 
  &&  “ (src_word1_distinct_cspaces <= UINT_MAX) ”
  &&  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
.

Definition ucos_CNode_Mint_partial_solve_wit_20_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_word1_distinct_cspaces <> rights_pre)) (PreH2 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH3 : (src_kind_distinct_cspaces = 1)) (PreH4 : (source_distinct_cspaces <> 0)) (PreH5 : (target_distinct_cspaces <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH11 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH12 : (func_capability_pre = slot_distinct_cspaces)) (PreH13 : (rights_pre = requested_distinct_cspaces)) (PreH14 : (0 <= dest_distinct_cspaces)) (PreH15 : (dest_distinct_cspaces < 64)) (PreH16 : (0 <= src_distinct_cspaces)) (PreH17 : (src_distinct_cspaces < 64)) (PreH18 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH20 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH21 : (0 <= slot_distinct_cspaces)) (PreH22 : (slot_distinct_cspaces <= 16)) (PreH23 : (target_distinct_cspaces <> 0)) (PreH24 : (source_distinct_cspaces <> 0)) (PreH25 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH26 : (0 <= requested_distinct_cspaces)) (PreH27 : (requested_distinct_cspaces <= UINT_MAX)) (PreH28 : (0 <= src_word1_distinct_cspaces)) (PreH29 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (src_word1_distinct_cspaces <> rights_pre) ” 
  &&  “ ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0) ” 
  &&  “ (src_kind_distinct_cspaces = 1) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_distinct_cspaces) ” 
  &&  “ (srcTask_Prio_pre = src_distinct_cspaces) ” 
  &&  “ (func_capability_pre = slot_distinct_cspaces) ” 
  &&  “ (rights_pre = requested_distinct_cspaces) ” 
  &&  “ (0 <= dest_distinct_cspaces) ” 
  &&  “ (dest_distinct_cspaces < 64) ” 
  &&  “ (0 <= src_distinct_cspaces) ” 
  &&  “ (src_distinct_cspaces < 64) ” 
  &&  “ (dest_distinct_cspaces <> src_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces) ” 
  &&  “ (0 <= slot_distinct_cspaces) ” 
  &&  “ (slot_distinct_cspaces <= 16) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> source_distinct_cspaces) ” 
  &&  “ (0 <= requested_distinct_cspaces) ” 
  &&  “ (requested_distinct_cspaces <= UINT_MAX) ” 
  &&  “ (0 <= src_word1_distinct_cspaces) ” 
  &&  “ (src_word1_distinct_cspaces <= UINT_MAX) ”
  &&  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
.

Definition ucos_CNode_Mint_partial_solve_wit_21_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (dst_word0_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_word1_distinct_cspaces <> rights_pre)) (PreH2 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH3 : (src_kind_distinct_cspaces = 1)) (PreH4 : (source_distinct_cspaces <> 0)) (PreH5 : (target_distinct_cspaces <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH11 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH12 : (func_capability_pre = slot_distinct_cspaces)) (PreH13 : (rights_pre = requested_distinct_cspaces)) (PreH14 : (0 <= dest_distinct_cspaces)) (PreH15 : (dest_distinct_cspaces < 64)) (PreH16 : (0 <= src_distinct_cspaces)) (PreH17 : (src_distinct_cspaces < 64)) (PreH18 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH20 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH21 : (0 <= slot_distinct_cspaces)) (PreH22 : (slot_distinct_cspaces <= 16)) (PreH23 : (target_distinct_cspaces <> 0)) (PreH24 : (source_distinct_cspaces <> 0)) (PreH25 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH26 : (0 <= requested_distinct_cspaces)) (PreH27 : (requested_distinct_cspaces <= UINT_MAX)) (PreH28 : (0 <= src_word1_distinct_cspaces)) (PreH29 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> dst_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (src_word1_distinct_cspaces <> rights_pre) ” 
  &&  “ ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0) ” 
  &&  “ (src_kind_distinct_cspaces = 1) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_distinct_cspaces) ” 
  &&  “ (srcTask_Prio_pre = src_distinct_cspaces) ” 
  &&  “ (func_capability_pre = slot_distinct_cspaces) ” 
  &&  “ (rights_pre = requested_distinct_cspaces) ” 
  &&  “ (0 <= dest_distinct_cspaces) ” 
  &&  “ (dest_distinct_cspaces < 64) ” 
  &&  “ (0 <= src_distinct_cspaces) ” 
  &&  “ (src_distinct_cspaces < 64) ” 
  &&  “ (dest_distinct_cspaces <> src_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces) ” 
  &&  “ (0 <= slot_distinct_cspaces) ” 
  &&  “ (slot_distinct_cspaces <= 16) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> source_distinct_cspaces) ” 
  &&  “ (0 <= requested_distinct_cspaces) ” 
  &&  “ (requested_distinct_cspaces <= UINT_MAX) ” 
  &&  “ (0 <= src_word1_distinct_cspaces) ” 
  &&  “ (src_word1_distinct_cspaces <= UINT_MAX) ”
  &&  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
.

Definition ucos_CNode_Mint_partial_solve_wit_22_shared_cspace := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_shared_cspace: Z) (word0_shared_cspace: Z) (old_kind_shared_cspace: Z) (target_shared_cspace: Z) (requested_shared_cspace: Z) (slot_shared_cspace: Z) (src_shared_cspace: Z) (dest_shared_cspace: Z) (PreH1 : (word1_shared_cspace <> rights_pre)) (PreH2 : ((Z.land (Z.lnot word1_shared_cspace) rights_pre) = 0)) (PreH3 : (old_kind_shared_cspace = 1)) (PreH4 : (target_shared_cspace <> 0)) (PreH5 : (target_shared_cspace <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_shared_cspace)) (PreH11 : (srcTask_Prio_pre = src_shared_cspace)) (PreH12 : (func_capability_pre = slot_shared_cspace)) (PreH13 : (rights_pre = requested_shared_cspace)) (PreH14 : (0 <= dest_shared_cspace)) (PreH15 : (dest_shared_cspace < 64)) (PreH16 : (0 <= src_shared_cspace)) (PreH17 : (src_shared_cspace < 64)) (PreH18 : (dest_shared_cspace <> src_shared_cspace)) (PreH19 : ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace)) (PreH20 : ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace)) (PreH21 : (0 <= slot_shared_cspace)) (PreH22 : (slot_shared_cspace <= 16)) (PreH23 : (target_shared_cspace <> 0)) (PreH24 : (0 <= requested_shared_cspace)) (PreH25 : (requested_shared_cspace <= UINT_MAX)) (PreH26 : (0 <= word1_shared_cspace)) (PreH27 : (word1_shared_cspace <= UINT_MAX)) ,
  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_shared_cspace * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
|--
  “ (word1_shared_cspace <> rights_pre) ” 
  &&  “ ((Z.land (Z.lnot word1_shared_cspace) rights_pre) = 0) ” 
  &&  “ (old_kind_shared_cspace = 1) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_shared_cspace) ” 
  &&  “ (srcTask_Prio_pre = src_shared_cspace) ” 
  &&  “ (func_capability_pre = slot_shared_cspace) ” 
  &&  “ (rights_pre = requested_shared_cspace) ” 
  &&  “ (0 <= dest_shared_cspace) ” 
  &&  “ (dest_shared_cspace < 64) ” 
  &&  “ (0 <= src_shared_cspace) ” 
  &&  “ (src_shared_cspace < 64) ” 
  &&  “ (dest_shared_cspace <> src_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (dest_shared_cspace) (32)) = dest_shared_cspace) ” 
  &&  “ ((unsigned_last_nbits (src_shared_cspace) (32)) = src_shared_cspace) ” 
  &&  “ (0 <= slot_shared_cspace) ” 
  &&  “ (slot_shared_cspace <= 16) ” 
  &&  “ (target_shared_cspace <> 0) ” 
  &&  “ (0 <= requested_shared_cspace) ” 
  &&  “ (requested_shared_cspace <= UINT_MAX) ” 
  &&  “ (0 <= word1_shared_cspace) ” 
  &&  “ (word1_shared_cspace <= UINT_MAX) ”
  &&  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_shared_cspace)
  **  ((&(((&((target_shared_cspace)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_shared_cspace)
.

Definition ucos_CNode_Mint_partial_solve_wit_23_same_priority := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (word1_same_priority: Z) (word0_same_priority: Z) (old_kind_same_priority: Z) (target_same_priority: Z) (requested_same_priority: Z) (slot_same_priority: Z) (prio_same_priority: Z) (PreH1 : (word1_same_priority <> rights_pre)) (PreH2 : ((Z.land (Z.lnot word1_same_priority) rights_pre) = 0)) (PreH3 : (old_kind_same_priority = 1)) (PreH4 : (target_same_priority <> 0)) (PreH5 : (target_same_priority <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = prio_same_priority)) (PreH11 : (srcTask_Prio_pre = prio_same_priority)) (PreH12 : (func_capability_pre = slot_same_priority)) (PreH13 : (rights_pre = requested_same_priority)) (PreH14 : (0 <= prio_same_priority)) (PreH15 : (prio_same_priority < 64)) (PreH16 : ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority)) (PreH17 : (0 <= slot_same_priority)) (PreH18 : (slot_same_priority <= 16)) (PreH19 : (target_same_priority <> 0)) (PreH20 : (0 <= requested_same_priority)) (PreH21 : (requested_same_priority <= UINT_MAX)) (PreH22 : (0 <= word1_same_priority)) (PreH23 : (word1_same_priority <= UINT_MAX)) ,
  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_same_priority * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
|--
  “ (word1_same_priority <> rights_pre) ” 
  &&  “ ((Z.land (Z.lnot word1_same_priority) rights_pre) = 0) ” 
  &&  “ (old_kind_same_priority = 1) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = prio_same_priority) ” 
  &&  “ (srcTask_Prio_pre = prio_same_priority) ” 
  &&  “ (func_capability_pre = slot_same_priority) ” 
  &&  “ (rights_pre = requested_same_priority) ” 
  &&  “ (0 <= prio_same_priority) ” 
  &&  “ (prio_same_priority < 64) ” 
  &&  “ ((unsigned_last_nbits (prio_same_priority) (32)) = prio_same_priority) ” 
  &&  “ (0 <= slot_same_priority) ” 
  &&  “ (slot_same_priority <= 16) ” 
  &&  “ (target_same_priority <> 0) ” 
  &&  “ (0 <= requested_same_priority) ” 
  &&  “ (requested_same_priority <= UINT_MAX) ” 
  &&  “ (0 <= word1_same_priority) ” 
  &&  “ (word1_same_priority <= UINT_MAX) ”
  &&  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> word0_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> word1_same_priority)
  **  ((&(((&((target_same_priority)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_same_priority)
.

Definition ucos_CNode_Mint_partial_solve_wit_24_distinct_cspaces := 
forall (rights_pre: Z) (func_capability_pre: Z) (srcTask_Prio_pre: Z) (destTask_Prio_pre: Z) (dst_word1_distinct_cspaces: Z) (src_word1_distinct_cspaces: Z) (src_word0_distinct_cspaces: Z) (src_kind_distinct_cspaces: Z) (source_distinct_cspaces: Z) (target_distinct_cspaces: Z) (requested_distinct_cspaces: Z) (slot_distinct_cspaces: Z) (src_distinct_cspaces: Z) (dest_distinct_cspaces: Z) (PreH1 : (src_word1_distinct_cspaces <> rights_pre)) (PreH2 : ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0)) (PreH3 : (src_kind_distinct_cspaces = 1)) (PreH4 : (source_distinct_cspaces <> 0)) (PreH5 : (target_distinct_cspaces <> 0)) (PreH6 : (srcTask_Prio_pre < 64)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (func_capability_pre <= 16)) (PreH9 : (0 <= func_capability_pre)) (PreH10 : (destTask_Prio_pre = dest_distinct_cspaces)) (PreH11 : (srcTask_Prio_pre = src_distinct_cspaces)) (PreH12 : (func_capability_pre = slot_distinct_cspaces)) (PreH13 : (rights_pre = requested_distinct_cspaces)) (PreH14 : (0 <= dest_distinct_cspaces)) (PreH15 : (dest_distinct_cspaces < 64)) (PreH16 : (0 <= src_distinct_cspaces)) (PreH17 : (src_distinct_cspaces < 64)) (PreH18 : (dest_distinct_cspaces <> src_distinct_cspaces)) (PreH19 : ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces)) (PreH20 : ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces)) (PreH21 : (0 <= slot_distinct_cspaces)) (PreH22 : (slot_distinct_cspaces <= 16)) (PreH23 : (target_distinct_cspaces <> 0)) (PreH24 : (source_distinct_cspaces <> 0)) (PreH25 : (target_distinct_cspaces <> source_distinct_cspaces)) (PreH26 : (0 <= requested_distinct_cspaces)) (PreH27 : (requested_distinct_cspaces <= UINT_MAX)) (PreH28 : (0 <= src_word1_distinct_cspaces)) (PreH29 : (src_word1_distinct_cspaces <= UINT_MAX)) ,
  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (slot_distinct_cspaces * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> dst_word1_distinct_cspaces)
|--
  “ (src_word1_distinct_cspaces <> rights_pre) ” 
  &&  “ ((Z.land (Z.lnot src_word1_distinct_cspaces) rights_pre) = 0) ” 
  &&  “ (src_kind_distinct_cspaces = 1) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (srcTask_Prio_pre < 64) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (func_capability_pre <= 16) ” 
  &&  “ (0 <= func_capability_pre) ” 
  &&  “ (destTask_Prio_pre = dest_distinct_cspaces) ” 
  &&  “ (srcTask_Prio_pre = src_distinct_cspaces) ” 
  &&  “ (func_capability_pre = slot_distinct_cspaces) ” 
  &&  “ (rights_pre = requested_distinct_cspaces) ” 
  &&  “ (0 <= dest_distinct_cspaces) ” 
  &&  “ (dest_distinct_cspaces < 64) ” 
  &&  “ (0 <= src_distinct_cspaces) ” 
  &&  “ (src_distinct_cspaces < 64) ” 
  &&  “ (dest_distinct_cspaces <> src_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (dest_distinct_cspaces) (32)) = dest_distinct_cspaces) ” 
  &&  “ ((unsigned_last_nbits (src_distinct_cspaces) (32)) = src_distinct_cspaces) ” 
  &&  “ (0 <= slot_distinct_cspaces) ” 
  &&  “ (slot_distinct_cspaces <= 16) ” 
  &&  “ (target_distinct_cspaces <> 0) ” 
  &&  “ (source_distinct_cspaces <> 0) ” 
  &&  “ (target_distinct_cspaces <> source_distinct_cspaces) ” 
  &&  “ (0 <= requested_distinct_cspaces) ” 
  &&  “ (requested_distinct_cspaces <= UINT_MAX) ” 
  &&  “ (0 <= src_word1_distinct_cspaces) ” 
  &&  “ (src_word1_distinct_cspaces <= UINT_MAX) ”
  &&  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> src_word0_distinct_cspaces)
  **  ((&(((&((target_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> src_word1_distinct_cspaces)
  **  ((&(((&((source_distinct_cspaces)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> src_kind_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (srcTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> source_distinct_cspaces)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_distinct_cspaces)
.

Module Type VC_Correct.


Axiom proof_of_ucos_CNode_Mint_safety_wit_1_class_invalid : ucos_CNode_Mint_safety_wit_1_class_invalid.
Axiom proof_of_ucos_CNode_Mint_safety_wit_2_prio_invalid : ucos_CNode_Mint_safety_wit_2_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_safety_wit_3_prio_invalid : ucos_CNode_Mint_safety_wit_3_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_safety_wit_4_null_same_priority : ucos_CNode_Mint_safety_wit_4_null_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_5_null_distinct_priorities : ucos_CNode_Mint_safety_wit_5_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_6_null_distinct_priorities : ucos_CNode_Mint_safety_wit_6_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_7_same_priority : ucos_CNode_Mint_safety_wit_7_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_8_shared_cspace : ucos_CNode_Mint_safety_wit_8_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_safety_wit_9_distinct_cspaces : ucos_CNode_Mint_safety_wit_9_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_safety_wit_10_distinct_cspaces : ucos_CNode_Mint_safety_wit_10_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_safety_wit_11_shared_cspace : ucos_CNode_Mint_safety_wit_11_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_safety_wit_12_same_priority : ucos_CNode_Mint_safety_wit_12_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_13_null_distinct_priorities : ucos_CNode_Mint_safety_wit_13_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_14_null_distinct_priorities : ucos_CNode_Mint_safety_wit_14_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_15_null_same_priority : ucos_CNode_Mint_safety_wit_15_null_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_16_prio_invalid : ucos_CNode_Mint_safety_wit_16_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_safety_wit_17_prio_invalid : ucos_CNode_Mint_safety_wit_17_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_safety_wit_18_class_invalid : ucos_CNode_Mint_safety_wit_18_class_invalid.
Axiom proof_of_ucos_CNode_Mint_safety_wit_19_prio_invalid : ucos_CNode_Mint_safety_wit_19_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_safety_wit_20_null_same_priority : ucos_CNode_Mint_safety_wit_20_null_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_21_null_distinct_priorities : ucos_CNode_Mint_safety_wit_21_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_22_null_distinct_priorities : ucos_CNode_Mint_safety_wit_22_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_23_same_priority : ucos_CNode_Mint_safety_wit_23_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_24_shared_cspace : ucos_CNode_Mint_safety_wit_24_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_safety_wit_25_distinct_cspaces : ucos_CNode_Mint_safety_wit_25_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_safety_wit_26_distinct_cspaces : ucos_CNode_Mint_safety_wit_26_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_safety_wit_27_shared_cspace : ucos_CNode_Mint_safety_wit_27_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_safety_wit_28_same_priority : ucos_CNode_Mint_safety_wit_28_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_29_null_distinct_priorities : ucos_CNode_Mint_safety_wit_29_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_30_null_distinct_priorities : ucos_CNode_Mint_safety_wit_30_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_31_null_same_priority : ucos_CNode_Mint_safety_wit_31_null_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_32_prio_invalid : ucos_CNode_Mint_safety_wit_32_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_safety_wit_33_null_same_priority : ucos_CNode_Mint_safety_wit_33_null_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_34_null_distinct_priorities : ucos_CNode_Mint_safety_wit_34_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_35_null_distinct_priorities : ucos_CNode_Mint_safety_wit_35_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_36_same_priority : ucos_CNode_Mint_safety_wit_36_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_37_shared_cspace : ucos_CNode_Mint_safety_wit_37_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_safety_wit_38_distinct_cspaces : ucos_CNode_Mint_safety_wit_38_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_safety_wit_39_same_priority : ucos_CNode_Mint_safety_wit_39_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_40_shared_cspace : ucos_CNode_Mint_safety_wit_40_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_safety_wit_41_distinct_cspaces : ucos_CNode_Mint_safety_wit_41_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_safety_wit_42_distinct_cspaces : ucos_CNode_Mint_safety_wit_42_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_safety_wit_43_shared_cspace : ucos_CNode_Mint_safety_wit_43_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_safety_wit_44_same_priority : ucos_CNode_Mint_safety_wit_44_same_priority.
Axiom proof_of_ucos_CNode_Mint_safety_wit_45_null_distinct_priorities : ucos_CNode_Mint_safety_wit_45_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_safety_wit_46_distinct_cspaces : ucos_CNode_Mint_safety_wit_46_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_safety_wit_47_shared_cspace : ucos_CNode_Mint_safety_wit_47_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_safety_wit_48_same_priority : ucos_CNode_Mint_safety_wit_48_same_priority.
Axiom proof_of_ucos_CNode_Mint_return_wit_1_distinct_cspaces : ucos_CNode_Mint_return_wit_1_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_return_wit_2_shared_cspace : ucos_CNode_Mint_return_wit_2_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_return_wit_3_same_priority : ucos_CNode_Mint_return_wit_3_same_priority.
Axiom proof_of_ucos_CNode_Mint_return_wit_4_distinct_cspaces : ucos_CNode_Mint_return_wit_4_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_return_wit_5_shared_cspace : ucos_CNode_Mint_return_wit_5_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_return_wit_6_same_priority : ucos_CNode_Mint_return_wit_6_same_priority.
Axiom proof_of_ucos_CNode_Mint_return_wit_7_same_priority : ucos_CNode_Mint_return_wit_7_same_priority.
Axiom proof_of_ucos_CNode_Mint_return_wit_8_shared_cspace : ucos_CNode_Mint_return_wit_8_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_return_wit_9_distinct_cspaces : ucos_CNode_Mint_return_wit_9_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_return_wit_10_distinct_cspaces : ucos_CNode_Mint_return_wit_10_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_return_wit_11_shared_cspace : ucos_CNode_Mint_return_wit_11_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_return_wit_12_same_priority : ucos_CNode_Mint_return_wit_12_same_priority.
Axiom proof_of_ucos_CNode_Mint_return_wit_13_null_distinct_priorities : ucos_CNode_Mint_return_wit_13_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_return_wit_14_null_distinct_priorities : ucos_CNode_Mint_return_wit_14_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_return_wit_15_null_same_priority : ucos_CNode_Mint_return_wit_15_null_same_priority.
Axiom proof_of_ucos_CNode_Mint_return_wit_16_null_distinct_priorities : ucos_CNode_Mint_return_wit_16_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_return_wit_17_prio_invalid : ucos_CNode_Mint_return_wit_17_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_return_wit_18_prio_invalid : ucos_CNode_Mint_return_wit_18_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_return_wit_19_prio_invalid : ucos_CNode_Mint_return_wit_19_prio_invalid.
Axiom proof_of_ucos_CNode_Mint_return_wit_20_class_invalid : ucos_CNode_Mint_return_wit_20_class_invalid.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_1_null_same_priority : ucos_CNode_Mint_partial_solve_wit_1_null_same_priority.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_2_null_distinct_priorities : ucos_CNode_Mint_partial_solve_wit_2_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_3_null_distinct_priorities : ucos_CNode_Mint_partial_solve_wit_3_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_4_same_priority : ucos_CNode_Mint_partial_solve_wit_4_same_priority.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_5_shared_cspace : ucos_CNode_Mint_partial_solve_wit_5_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_6_distinct_cspaces : ucos_CNode_Mint_partial_solve_wit_6_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_7_null_same_priority : ucos_CNode_Mint_partial_solve_wit_7_null_same_priority.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_8_null_distinct_priorities : ucos_CNode_Mint_partial_solve_wit_8_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_9_null_distinct_priorities : ucos_CNode_Mint_partial_solve_wit_9_null_distinct_priorities.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_10_same_priority : ucos_CNode_Mint_partial_solve_wit_10_same_priority.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_11_shared_cspace : ucos_CNode_Mint_partial_solve_wit_11_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_12_distinct_cspaces : ucos_CNode_Mint_partial_solve_wit_12_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_13_same_priority : ucos_CNode_Mint_partial_solve_wit_13_same_priority.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_14_shared_cspace : ucos_CNode_Mint_partial_solve_wit_14_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_15_distinct_cspaces : ucos_CNode_Mint_partial_solve_wit_15_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_16_distinct_cspaces : ucos_CNode_Mint_partial_solve_wit_16_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_17_shared_cspace : ucos_CNode_Mint_partial_solve_wit_17_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_18_same_priority : ucos_CNode_Mint_partial_solve_wit_18_same_priority.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_19_distinct_cspaces : ucos_CNode_Mint_partial_solve_wit_19_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_20_distinct_cspaces : ucos_CNode_Mint_partial_solve_wit_20_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_21_distinct_cspaces : ucos_CNode_Mint_partial_solve_wit_21_distinct_cspaces.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_22_shared_cspace : ucos_CNode_Mint_partial_solve_wit_22_shared_cspace.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_23_same_priority : ucos_CNode_Mint_partial_solve_wit_23_same_priority.
Axiom proof_of_ucos_CNode_Mint_partial_solve_wit_24_distinct_cspaces : ucos_CNode_Mint_partial_solve_wit_24_distinct_cspaces.

End VC_Correct.
