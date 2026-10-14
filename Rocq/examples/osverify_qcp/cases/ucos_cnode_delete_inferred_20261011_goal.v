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
Require Import SimpleC.EE.osverify_qcp.cases.ucos_cnode_delete_inferred_20261011_lib.
Local Open Scope sac.

(*----- Function ucos_CNode_Delete -----*)

Definition ucos_CNode_Delete_safety_wit_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (space <> 0)) (PreH8 : (old_type <> 1)) (PreH9 : (old_type <> 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_2 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (space <> 0)) (PreH8 : (old_type = 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_3 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (space <> 0)) (PreH8 : (old_type = 1)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_4 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (space: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (space = 0)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_5 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (func_capability_pre < 255)) (PreH2 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (func_capability_pre >= 255)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_6 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (func_capability_pre < 255)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (space <> 0)) (PreH9 : (old_type <> 1)) (PreH10 : (old_type <> 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_7 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (func_capability_pre < 255)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (space <> 0)) (PreH9 : (old_type = 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_8 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (func_capability_pre < 255)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (space <> 0)) (PreH9 : (old_type = 1)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_9 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (space: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (func_capability_pre < 255)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (space = 0)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_10 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (destTask_Prio_pre >= 64)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_11 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (func_capability_pre < 255)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (space <> 0)) (PreH9 : (old_type <> 1)) (PreH10 : (old_type <> 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_safety_wit_12 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (func_capability_pre < 255)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (space <> 0)) (PreH9 : (old_type = 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_safety_wit_13 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (func_capability_pre < 255)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (space <> 0)) (PreH9 : (old_type = 1)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_safety_wit_14 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (space: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (func_capability_pre < 255)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (space = 0)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_safety_wit_15 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (space = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (space <> 0)) (PreH10 : (old_type <> 1)) (PreH11 : (old_type <> 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_16 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (space = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (space <> 0)) (PreH10 : (old_type = 2)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_17 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (space = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (space <> 0)) (PreH10 : (old_type = 1)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_18 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (space: Z) (PreH1 : (space <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (space = 0)) ,
  ((( &( "cap1" ) )) # Ptr  |->_)
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_19 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type <> 1)) (PreH2 : (space <> 0)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre < 255)) (PreH5 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH6 : (0 <= destTask_Prio_pre)) (PreH7 : (destTask_Prio_pre <= 255)) (PreH8 : (func_capability_pre < 255)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (space <> 0)) (PreH11 : (old_type = 1)) ,
  ((( &( "cap1" ) )) # Ptr  |-> &(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_20 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 1)) (PreH2 : (space <> 0)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre < 255)) (PreH5 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH6 : (0 <= destTask_Prio_pre)) (PreH7 : (destTask_Prio_pre <= 255)) (PreH8 : (func_capability_pre < 255)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (space <> 0)) (PreH11 : (old_type = 2)) ,
  ((( &( "cap1" ) )) # Ptr  |-> &(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_21 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 1)) (PreH2 : (space <> 0)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre < 255)) (PreH5 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH6 : (0 <= destTask_Prio_pre)) (PreH7 : (destTask_Prio_pre <= 255)) (PreH8 : (func_capability_pre < 255)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (space <> 0)) (PreH11 : (old_type <> 1)) (PreH12 : (old_type <> 2)) ,
  ((( &( "cap1" ) )) # Ptr  |-> &(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_22 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type <> 1)) (PreH13 : (old_type <> 2)) ,
  ((( &( "cap1" ) )) # Ptr  |-> &(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_23 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type <> 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type = 2)) ,
  ((( &( "cap1" ) )) # Ptr  |-> &(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
|--
  “ False ”
.

Definition ucos_CNode_Delete_safety_wit_24 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type = 2)) ,
  ((( &( "cap1" ) )) # Ptr  |-> &(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability"))
  **  ((( &( "pCSpace1" ) )) # Ptr  |-> space)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "func_capability" ) )) # UInt  |-> func_capability_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |->_)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_CNode_Delete_return_wit_1 := 
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 1)) (PreH2 : (space <> 0)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre < 255)) (PreH5 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH6 : (0 <= destTask_Prio_pre)) (PreH7 : (destTask_Prio_pre <= 255)) (PreH8 : (func_capability_pre < 255)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (space <> 0)) (PreH11 : (old_type = 1)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> 0)
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space old_type 0 ) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (space <> 0) ” 
  &&  “ (old_type = 1) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> (cd_cap_type_after (old_type)))
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> 0)
) \/
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 1)) (PreH2 : (space <> 0)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre < 255)) (PreH5 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH6 : (0 <= destTask_Prio_pre)) (PreH7 : (destTask_Prio_pre <= 255)) (PreH8 : (func_capability_pre < 255)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (space <> 0)) (PreH11 : (old_type = 1)) ,
  TT && emp 
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space 1 0 ) ” 
  &&  “ (0 = (cd_cap_type_after (1))) ”
  &&  emp
).

Definition ucos_CNode_Delete_return_wit_1_split_goal_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 1)) (PreH2 : (space <> 0)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre < 255)) (PreH5 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH6 : (0 <= destTask_Prio_pre)) (PreH7 : (destTask_Prio_pre <= 255)) (PreH8 : (func_capability_pre < 255)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (space <> 0)) (PreH11 : (old_type = 1)) ,
  (cd_result destTask_Prio_pre func_capability_pre space 1 0 )
.

Definition ucos_CNode_Delete_return_wit_1_split_goal_2 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 1)) (PreH2 : (space <> 0)) (PreH3 : (destTask_Prio_pre < 64)) (PreH4 : (func_capability_pre < 255)) (PreH5 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH6 : (0 <= destTask_Prio_pre)) (PreH7 : (destTask_Prio_pre <= 255)) (PreH8 : (func_capability_pre < 255)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (space <> 0)) (PreH11 : (old_type = 1)) ,
  (0 = (cd_cap_type_after (1)))
.

Definition ucos_CNode_Delete_return_wit_2 := 
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type = 2)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> 0)
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space old_type 0 ) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (space <> 0) ” 
  &&  “ (old_type = 2) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> (cd_cap_type_after (old_type)))
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "slot_type")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_right")) # UInt  |-> 0)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t")) # Ptr  |-> 0)
) \/
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type = 2)) ,
  TT && emp 
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space 2 0 ) ” 
  &&  “ (0 = (cd_cap_type_after (2))) ”
  &&  emp
).

Definition ucos_CNode_Delete_return_wit_2_split_goal_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type = 2)) ,
  (cd_result destTask_Prio_pre func_capability_pre space 2 0 )
.

Definition ucos_CNode_Delete_return_wit_2_split_goal_2 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type = 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type = 2)) ,
  (0 = (cd_cap_type_after (2)))
.

Definition ucos_CNode_Delete_return_wit_3 := 
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type <> 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type <> 1)) (PreH13 : (old_type <> 2)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (space <> 0) ” 
  &&  “ (old_type <> 1) ” 
  &&  “ (old_type <> 2) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
  **  ((&(((&((space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (func_capability_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> (cd_cap_type_after (old_type)))
) \/
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type <> 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type <> 1)) (PreH13 : (old_type <> 2)) ,
  TT && emp 
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ” 
  &&  “ (old_type = (cd_cap_type_after (old_type))) ”
  &&  emp
).

Definition ucos_CNode_Delete_return_wit_3_split_goal_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type <> 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type <> 1)) (PreH13 : (old_type <> 2)) ,
  (cd_result destTask_Prio_pre func_capability_pre space old_type 9 )
.

Definition ucos_CNode_Delete_return_wit_3_split_goal_2 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (old_type <> 2)) (PreH2 : (old_type <> 1)) (PreH3 : (space <> 0)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (func_capability_pre < 255)) (PreH6 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (func_capability_pre < 255)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (space <> 0)) (PreH12 : (old_type <> 1)) (PreH13 : (old_type <> 2)) ,
  (old_type = (cd_cap_type_after (old_type)))
.

Definition ucos_CNode_Delete_return_wit_4 := 
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (space = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (space = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ” 
  &&  “ (func_capability_pre < 255) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (space = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> space)
) \/
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (space = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (space = 0)) ,
  TT && emp 
|--
  “ (cd_result destTask_Prio_pre func_capability_pre 0 old_type 9 ) ”
  &&  emp
).

Definition ucos_CNode_Delete_return_wit_4_split_goal_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (space = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (func_capability_pre < 255)) (PreH4 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (func_capability_pre < 255)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (space = 0)) ,
  (cd_result destTask_Prio_pre func_capability_pre 0 old_type 9 )
.

Definition ucos_CNode_Delete_return_wit_5 := 
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (destTask_Prio_pre >= 64)) ,
  TT && emp 
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ” 
  &&  “ (destTask_Prio_pre >= 64) ”
  &&  emp
) \/
(
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (destTask_Prio_pre >= 64)) ,
  TT && emp 
|--
  “ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ”
  &&  emp
).

Definition ucos_CNode_Delete_return_wit_5_split_goal_1 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (func_capability_pre < 255)) (PreH3 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (destTask_Prio_pre >= 64)) ,
  (cd_result destTask_Prio_pre func_capability_pre space old_type 9 )
.

Definition ucos_CNode_Delete_return_wit_6 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (func_capability_pre >= 255)) ,
  TT && emp 
|--
  (“ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ” 
  &&  “ (func_capability_pre >= 255) ”
  &&  emp)
  ||
  (“ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ” 
  &&  “ (destTask_Prio_pre >= 64) ”
  &&  emp)
.

Definition ucos_CNode_Delete_return_wit_7 := 
forall (func_capability_pre: Z) (destTask_Prio_pre: Z) (old_type: Z) (space: Z) (PreH1 : (func_capability_pre >= 255)) (PreH2 : (cd_input_domain destTask_Prio_pre func_capability_pre )) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (destTask_Prio_pre >= 64)) ,
  TT && emp 
|--
  (“ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ” 
  &&  “ (func_capability_pre >= 255) ”
  &&  emp)
  ||
  (“ (cd_result destTask_Prio_pre func_capability_pre space old_type 9 ) ” 
  &&  “ (destTask_Prio_pre >= 64) ”
  &&  emp)
.

Module Type VC_Correct.


Axiom proof_of_ucos_CNode_Delete_safety_wit_1 : ucos_CNode_Delete_safety_wit_1.
Axiom proof_of_ucos_CNode_Delete_safety_wit_2 : ucos_CNode_Delete_safety_wit_2.
Axiom proof_of_ucos_CNode_Delete_safety_wit_3 : ucos_CNode_Delete_safety_wit_3.
Axiom proof_of_ucos_CNode_Delete_safety_wit_4 : ucos_CNode_Delete_safety_wit_4.
Axiom proof_of_ucos_CNode_Delete_safety_wit_5 : ucos_CNode_Delete_safety_wit_5.
Axiom proof_of_ucos_CNode_Delete_safety_wit_6 : ucos_CNode_Delete_safety_wit_6.
Axiom proof_of_ucos_CNode_Delete_safety_wit_7 : ucos_CNode_Delete_safety_wit_7.
Axiom proof_of_ucos_CNode_Delete_safety_wit_8 : ucos_CNode_Delete_safety_wit_8.
Axiom proof_of_ucos_CNode_Delete_safety_wit_9 : ucos_CNode_Delete_safety_wit_9.
Axiom proof_of_ucos_CNode_Delete_safety_wit_10 : ucos_CNode_Delete_safety_wit_10.
Axiom proof_of_ucos_CNode_Delete_safety_wit_11 : ucos_CNode_Delete_safety_wit_11.
Axiom proof_of_ucos_CNode_Delete_safety_wit_12 : ucos_CNode_Delete_safety_wit_12.
Axiom proof_of_ucos_CNode_Delete_safety_wit_13 : ucos_CNode_Delete_safety_wit_13.
Axiom proof_of_ucos_CNode_Delete_safety_wit_14 : ucos_CNode_Delete_safety_wit_14.
Axiom proof_of_ucos_CNode_Delete_safety_wit_15 : ucos_CNode_Delete_safety_wit_15.
Axiom proof_of_ucos_CNode_Delete_safety_wit_16 : ucos_CNode_Delete_safety_wit_16.
Axiom proof_of_ucos_CNode_Delete_safety_wit_17 : ucos_CNode_Delete_safety_wit_17.
Axiom proof_of_ucos_CNode_Delete_safety_wit_18 : ucos_CNode_Delete_safety_wit_18.
Axiom proof_of_ucos_CNode_Delete_safety_wit_19 : ucos_CNode_Delete_safety_wit_19.
Axiom proof_of_ucos_CNode_Delete_safety_wit_20 : ucos_CNode_Delete_safety_wit_20.
Axiom proof_of_ucos_CNode_Delete_safety_wit_21 : ucos_CNode_Delete_safety_wit_21.
Axiom proof_of_ucos_CNode_Delete_safety_wit_22 : ucos_CNode_Delete_safety_wit_22.
Axiom proof_of_ucos_CNode_Delete_safety_wit_23 : ucos_CNode_Delete_safety_wit_23.
Axiom proof_of_ucos_CNode_Delete_safety_wit_24 : ucos_CNode_Delete_safety_wit_24.
Axiom proof_of_ucos_CNode_Delete_return_wit_1 : ucos_CNode_Delete_return_wit_1.
Axiom proof_of_ucos_CNode_Delete_return_wit_2 : ucos_CNode_Delete_return_wit_2.
Axiom proof_of_ucos_CNode_Delete_return_wit_3 : ucos_CNode_Delete_return_wit_3.
Axiom proof_of_ucos_CNode_Delete_return_wit_4 : ucos_CNode_Delete_return_wit_4.
Axiom proof_of_ucos_CNode_Delete_return_wit_5 : ucos_CNode_Delete_return_wit_5.
Axiom proof_of_ucos_CNode_Delete_return_wit_6 : ucos_CNode_Delete_return_wit_6.
Axiom proof_of_ucos_CNode_Delete_return_wit_7 : ucos_CNode_Delete_return_wit_7.

End VC_Correct.
