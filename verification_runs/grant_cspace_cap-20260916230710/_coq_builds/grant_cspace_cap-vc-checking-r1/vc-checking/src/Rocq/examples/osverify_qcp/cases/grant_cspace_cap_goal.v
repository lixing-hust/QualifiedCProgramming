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
Require Import SimpleC.EE.osverify_qcp.cap_model.
Local Open Scope sac.

(*----- Function grant_cspace_cap -----*)

Definition grant_cspace_cap_safety_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (old_os_prio: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest < 63)) (PreH13 : (current_tcb <> 0)) (PreH14 : (0 <= current_prio)) (PreH15 : (current_prio < 64)) (PreH16 : (current_prio <> dest)) (PreH17 : (current_space <> target)) (PreH18 : (current_space <> 0)) (PreH19 : (class > 16)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> old_os_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (old_os_prio: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest < 63)) (PreH13 : (current_tcb <> 0)) (PreH14 : (0 <= current_prio)) (PreH15 : (current_prio < 64)) (PreH16 : (current_prio <> dest)) (PreH17 : (current_space <> target)) (PreH18 : (current_space <> 0)) (PreH19 : (class <= 16)) (PreH20 : (target <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> old_os_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (old_os_prio: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest < 63)) (PreH13 : (current_tcb <> 0)) (PreH14 : (0 <= current_prio)) (PreH15 : (current_prio < 64)) (PreH16 : (current_prio <> dest)) (PreH17 : (current_space <> target)) (PreH18 : (current_space <> 0)) (PreH19 : (class <= 16)) (PreH20 : (target = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> old_os_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (current_space: Z) (old_os_prio: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest < 63)) (PreH13 : (current_tcb <> 0)) (PreH14 : (0 <= current_prio)) (PreH15 : (current_prio < 64)) (PreH16 : (current_prio <> dest)) (PreH17 : (current_space <> target)) (PreH18 : (current_space = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> old_os_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest >= 63)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest < 63)) (PreH13 : (current_tcb <> 0)) (PreH14 : (0 <= current_prio)) (PreH15 : (current_prio < 64)) (PreH16 : (current_prio <> dest)) (PreH17 : (current_space <> target)) (PreH18 : (current_space <> 0)) (PreH19 : (class > 16)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_7 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest < 63)) (PreH13 : (current_tcb <> 0)) (PreH14 : (0 <= current_prio)) (PreH15 : (current_prio < 64)) (PreH16 : (current_prio <> dest)) (PreH17 : (current_space <> target)) (PreH18 : (current_space <> 0)) (PreH19 : (class <= 16)) (PreH20 : (target <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest < 63)) (PreH13 : (current_tcb <> 0)) (PreH14 : (0 <= current_prio)) (PreH15 : (current_prio < 64)) (PreH16 : (current_prio <> dest)) (PreH17 : (current_space <> target)) (PreH18 : (current_space <> 0)) (PreH19 : (class <= 16)) (PreH20 : (target = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (current_space: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest < 63)) (PreH13 : (current_tcb <> 0)) (PreH14 : (0 <= current_prio)) (PreH15 : (current_prio < 64)) (PreH16 : (current_prio <> dest)) (PreH17 : (current_space <> target)) (PreH18 : (current_space = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (current_space = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (dest < 63)) (PreH14 : (current_tcb <> 0)) (PreH15 : (0 <= current_prio)) (PreH16 : (current_prio < 64)) (PreH17 : (current_prio <> dest)) (PreH18 : (current_space <> target)) (PreH19 : (current_space <> 0)) (PreH20 : (class > 16)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_11 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (current_space = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (dest < 63)) (PreH14 : (current_tcb <> 0)) (PreH15 : (0 <= current_prio)) (PreH16 : (current_prio < 64)) (PreH17 : (current_prio <> dest)) (PreH18 : (current_space <> target)) (PreH19 : (current_space <> 0)) (PreH20 : (class <= 16)) (PreH21 : (target <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_12 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (current_space = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (dest < 63)) (PreH14 : (current_tcb <> 0)) (PreH15 : (0 <= current_prio)) (PreH16 : (current_prio < 64)) (PreH17 : (current_prio <> dest)) (PreH18 : (current_space <> target)) (PreH19 : (current_space <> 0)) (PreH20 : (class <= 16)) (PreH21 : (target = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_13 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (current_space: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (current_space <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (dest < 63)) (PreH14 : (current_tcb <> 0)) (PreH15 : (0 <= current_prio)) (PreH16 : (current_prio < 64)) (PreH17 : (current_prio <> dest)) (PreH18 : (current_space <> target)) (PreH19 : (current_space = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_14_callee_null := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 11)) (PreH3 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_15_callee_success := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (grant_cap_transition retval class right old_type old_content old_right 1 class (Z.lor (Z.land old_right 4095) right) )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (current_space <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (destTask_Prio_pre = dest)) (PreH8 : (cap_Class_pre = class)) (PreH9 : (cap_Right_pre = right)) (PreH10 : (0 <= dest)) (PreH11 : (dest <= 255)) (PreH12 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH13 : (0 <= class)) (PreH14 : (class <= UINT_MAX)) (PreH15 : (0 <= right)) (PreH16 : (right <= UINT_MAX)) (PreH17 : (dest < 63)) (PreH18 : (current_tcb <> 0)) (PreH19 : (0 <= current_prio)) (PreH20 : (current_prio < 64)) (PreH21 : (current_prio <> dest)) (PreH22 : (current_space <> target)) (PreH23 : (current_space <> 0)) (PreH24 : (class <= 16)) (PreH25 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
  **  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_16_callee_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 11)) (PreH3 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class > 16)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_17_callee_null := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 11)) (PreH3 : (parent = current_prio)) (PreH4 : ((Z.land grant_right 64) <> 0)) (PreH5 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH6 : (current_space <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (destTask_Prio_pre = dest)) (PreH9 : (cap_Class_pre = class)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (0 <= dest)) (PreH12 : (dest <= 255)) (PreH13 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH14 : (0 <= class)) (PreH15 : (class <= UINT_MAX)) (PreH16 : (0 <= right)) (PreH17 : (right <= UINT_MAX)) (PreH18 : (dest < 63)) (PreH19 : (current_tcb <> 0)) (PreH20 : (0 <= current_prio)) (PreH21 : (current_prio < 64)) (PreH22 : (current_prio <> dest)) (PreH23 : (current_space <> target)) (PreH24 : (current_space <> 0)) (PreH25 : (class <= 16)) (PreH26 : (target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_18_callee_success := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (grant_cap_transition retval class right old_type old_content old_right 1 class (Z.lor (Z.land old_right 4095) right) )) (PreH4 : (parent = current_prio)) (PreH5 : ((Z.land grant_right 64) <> 0)) (PreH6 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH7 : (current_space <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (destTask_Prio_pre = dest)) (PreH10 : (cap_Class_pre = class)) (PreH11 : (cap_Right_pre = right)) (PreH12 : (0 <= dest)) (PreH13 : (dest <= 255)) (PreH14 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH15 : (0 <= class)) (PreH16 : (class <= UINT_MAX)) (PreH17 : (0 <= right)) (PreH18 : (right <= UINT_MAX)) (PreH19 : (dest < 63)) (PreH20 : (current_tcb <> 0)) (PreH21 : (0 <= current_prio)) (PreH22 : (current_prio < 64)) (PreH23 : (current_prio <> dest)) (PreH24 : (current_space <> target)) (PreH25 : (current_space <> 0)) (PreH26 : (class <= 16)) (PreH27 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_19_callee_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 11)) (PreH3 : (parent = current_prio)) (PreH4 : ((Z.land grant_right 64) <> 0)) (PreH5 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH6 : (current_space <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (destTask_Prio_pre = dest)) (PreH9 : (cap_Class_pre = class)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (0 <= dest)) (PreH12 : (dest <= 255)) (PreH13 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH14 : (0 <= class)) (PreH15 : (class <= UINT_MAX)) (PreH16 : (0 <= right)) (PreH17 : (right <= UINT_MAX)) (PreH18 : (dest < 63)) (PreH19 : (current_tcb <> 0)) (PreH20 : (0 <= current_prio)) (PreH21 : (current_prio < 64)) (PreH22 : (current_prio <> dest)) (PreH23 : (current_space <> target)) (PreH24 : (current_space <> 0)) (PreH25 : (class > 16)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  “ False ”
.

Definition grant_cspace_cap_return_wit_1 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target = 0)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ (parent <> current_prio) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target = 0)) ,
  TT && emp 
|--
  “ (running <> 0) ”
  &&  emp
).

Definition grant_cspace_cap_return_wit_1_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target = 0)) ,
  (running <> 0)
.

Definition grant_cspace_cap_return_wit_2 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target <> 0)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ (parent <> current_prio) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target <> 0)) ,
  TT && emp 
|--
  “ (running <> 0) ”
  &&  emp
).

Definition grant_cspace_cap_return_wit_2_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target <> 0)) ,
  (running <> 0)
.

Definition grant_cspace_cap_return_wit_3 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class > 16)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  “ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ (parent <> current_prio) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class > 16)) ,
  TT && emp 
|--
  “ (running <> 0) ”
  &&  emp
).

Definition grant_cspace_cap_return_wit_3_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent <> current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class > 16)) ,
  (running <> 0)
.

Definition grant_cspace_cap_return_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((Z.land grant_right 64) = 0)) (PreH2 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH3 : (current_space <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (destTask_Prio_pre = dest)) (PreH6 : (cap_Class_pre = class)) (PreH7 : (cap_Right_pre = right)) (PreH8 : (0 <= dest)) (PreH9 : (dest <= 255)) (PreH10 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH11 : (0 <= class)) (PreH12 : (class <= UINT_MAX)) (PreH13 : (0 <= right)) (PreH14 : (right <= UINT_MAX)) (PreH15 : (dest < 63)) (PreH16 : (current_tcb <> 0)) (PreH17 : (0 <= current_prio)) (PreH18 : (current_prio < 64)) (PreH19 : (current_prio <> dest)) (PreH20 : (current_space <> target)) (PreH21 : (current_space <> 0)) (PreH22 : (class > 16)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ (parent <> current_prio) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ ((Z.land grant_right 64) = 0) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent))
.

Definition grant_cspace_cap_return_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((Z.land grant_right 64) = 0)) (PreH2 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH3 : (current_space <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (destTask_Prio_pre = dest)) (PreH6 : (cap_Class_pre = class)) (PreH7 : (cap_Right_pre = right)) (PreH8 : (0 <= dest)) (PreH9 : (dest <= 255)) (PreH10 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH11 : (0 <= class)) (PreH12 : (class <= UINT_MAX)) (PreH13 : (0 <= right)) (PreH14 : (right <= UINT_MAX)) (PreH15 : (dest < 63)) (PreH16 : (current_tcb <> 0)) (PreH17 : (0 <= current_prio)) (PreH18 : (current_prio < 64)) (PreH19 : (current_prio <> dest)) (PreH20 : (current_space <> target)) (PreH21 : (current_space <> 0)) (PreH22 : (class <= 16)) (PreH23 : (target <> 0)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ (parent <> current_prio) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ ((Z.land grant_right 64) = 0) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right))
.

Definition grant_cspace_cap_return_wit_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((Z.land grant_right 64) = 0)) (PreH2 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH3 : (current_space <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (destTask_Prio_pre = dest)) (PreH6 : (cap_Class_pre = class)) (PreH7 : (cap_Right_pre = right)) (PreH8 : (0 <= dest)) (PreH9 : (dest <= 255)) (PreH10 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH11 : (0 <= class)) (PreH12 : (class <= UINT_MAX)) (PreH13 : (0 <= right)) (PreH14 : (right <= UINT_MAX)) (PreH15 : (dest < 63)) (PreH16 : (current_tcb <> 0)) (PreH17 : (0 <= current_prio)) (PreH18 : (current_prio < 64)) (PreH19 : (current_prio <> dest)) (PreH20 : (current_space <> target)) (PreH21 : (current_space <> 0)) (PreH22 : (class <= 16)) (PreH23 : (target = 0)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ (parent <> current_prio) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running <> 0) ” 
  &&  “ ((Z.land grant_right 64) = 0) ” 
  &&  “ (252 = 252) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target))
.

Definition grant_cspace_cap_return_wit_7_callee_null := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 11)) (PreH3 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ (target = 0) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running = 0) ” 
  &&  “ (target = 0) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target))
.

Definition grant_cspace_cap_return_wit_8_callee_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 11)) (PreH3 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class > 16)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ (target = 0) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ (class > 16) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running = 0) ” 
  &&  “ (target = 0) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running = 0) ” 
  &&  “ (class > 16) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent))
.

Definition grant_cspace_cap_return_wit_9_callee_null := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 11)) (PreH3 : (parent = current_prio)) (PreH4 : ((Z.land grant_right 64) <> 0)) (PreH5 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH6 : (current_space <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (destTask_Prio_pre = dest)) (PreH9 : (cap_Class_pre = class)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (0 <= dest)) (PreH12 : (dest <= 255)) (PreH13 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH14 : (0 <= class)) (PreH15 : (class <= UINT_MAX)) (PreH16 : (0 <= right)) (PreH17 : (right <= UINT_MAX)) (PreH18 : (dest < 63)) (PreH19 : (current_tcb <> 0)) (PreH20 : (0 <= current_prio)) (PreH21 : (current_prio < 64)) (PreH22 : (current_prio <> dest)) (PreH23 : (current_space <> target)) (PreH24 : (current_space <> 0)) (PreH25 : (class <= 16)) (PreH26 : (target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> 0)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  “ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ (target = 0) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
.

Definition grant_cspace_cap_return_wit_10_callee_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 11)) (PreH3 : (parent = current_prio)) (PreH4 : ((Z.land grant_right 64) <> 0)) (PreH5 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH6 : (current_space <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (destTask_Prio_pre = dest)) (PreH9 : (cap_Class_pre = class)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (0 <= dest)) (PreH12 : (dest <= 255)) (PreH13 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH14 : (0 <= class)) (PreH15 : (class <= UINT_MAX)) (PreH16 : (0 <= right)) (PreH17 : (right <= UINT_MAX)) (PreH18 : (dest < 63)) (PreH19 : (current_tcb <> 0)) (PreH20 : (0 <= current_prio)) (PreH21 : (current_prio < 64)) (PreH22 : (current_prio <> dest)) (PreH23 : (current_space <> target)) (PreH24 : (current_space <> 0)) (PreH25 : (class > 16)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ (target = 0) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ (class > 16) ” 
  &&  “ (11 = 11) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent))
.

Definition grant_cspace_cap_return_wit_11_callee_success := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (grant_cap_transition retval class right old_type old_content old_right 1 class (Z.lor (Z.land old_right 4095) right) )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (current_space <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (destTask_Prio_pre = dest)) (PreH8 : (cap_Class_pre = class)) (PreH9 : (cap_Right_pre = right)) (PreH10 : (0 <= dest)) (PreH11 : (dest <= 255)) (PreH12 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH13 : (0 <= class)) (PreH14 : (class <= UINT_MAX)) (PreH15 : (0 <= right)) (PreH16 : (right <= UINT_MAX)) (PreH17 : (dest < 63)) (PreH18 : (current_tcb <> 0)) (PreH19 : (0 <= current_prio)) (PreH20 : (current_prio < 64)) (PreH21 : (current_prio <> dest)) (PreH22 : (current_space <> target)) (PreH23 : (current_space <> 0)) (PreH24 : (class <= 16)) (PreH25 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right)))
  ||
  (“ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (running = 0) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right)))
.

Definition grant_cspace_cap_return_wit_12_callee_success := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (grant_cap_transition retval class right old_type old_content old_right 1 class (Z.lor (Z.land old_right 4095) right) )) (PreH4 : (parent = current_prio)) (PreH5 : ((Z.land grant_right 64) <> 0)) (PreH6 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH7 : (current_space <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (destTask_Prio_pre = dest)) (PreH10 : (cap_Class_pre = class)) (PreH11 : (cap_Right_pre = right)) (PreH12 : (0 <= dest)) (PreH13 : (dest <= 255)) (PreH14 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH15 : (0 <= class)) (PreH16 : (class <= UINT_MAX)) (PreH17 : (0 <= right)) (PreH18 : (right <= UINT_MAX)) (PreH19 : (dest < 63)) (PreH20 : (current_tcb <> 0)) (PreH21 : (0 <= current_prio)) (PreH22 : (current_prio < 64)) (PreH23 : (current_prio <> dest)) (PreH24 : (current_space <> target)) (PreH25 : (current_space <> 0)) (PreH26 : (class <= 16)) (PreH27 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  “ (dest < 63) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
.

Definition grant_cspace_cap_return_wit_13 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (current_space: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (current_space = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (dest < 63)) (PreH14 : (current_tcb <> 0)) (PreH15 : (0 <= current_prio)) (PreH16 : (current_prio < 64)) (PreH17 : (current_prio <> dest)) (PreH18 : (current_space <> target)) (PreH19 : (current_space = 0)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
|--
  “ (dest < 63) ” 
  &&  “ (current_space = 0) ” 
  &&  “ (11 = 11) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
.

Definition grant_cspace_cap_return_wit_14 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (dest >= 63)) ,
  TT && emp 
|--
  “ (42 = 42) ” 
  &&  “ (dest >= 63) ”
  &&  emp
.

Definition grant_cspace_cap_partial_solve_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((Z.land grant_right 64) <> 0)) (PreH2 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH3 : (current_space <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (destTask_Prio_pre = dest)) (PreH6 : (cap_Class_pre = class)) (PreH7 : (cap_Right_pre = right)) (PreH8 : (0 <= dest)) (PreH9 : (dest <= 255)) (PreH10 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH11 : (0 <= class)) (PreH12 : (class <= UINT_MAX)) (PreH13 : (0 <= right)) (PreH14 : (right <= UINT_MAX)) (PreH15 : (dest < 63)) (PreH16 : (current_tcb <> 0)) (PreH17 : (0 <= current_prio)) (PreH18 : (current_prio < 64)) (PreH19 : (current_prio <> dest)) (PreH20 : (current_space <> target)) (PreH21 : (current_space <> 0)) (PreH22 : (class <= 16)) (PreH23 : (target = 0)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) <> 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
.

Definition grant_cspace_cap_partial_solve_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((Z.land grant_right 64) <> 0)) (PreH2 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH3 : (current_space <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (destTask_Prio_pre = dest)) (PreH6 : (cap_Class_pre = class)) (PreH7 : (cap_Right_pre = right)) (PreH8 : (0 <= dest)) (PreH9 : (dest <= 255)) (PreH10 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH11 : (0 <= class)) (PreH12 : (class <= UINT_MAX)) (PreH13 : (0 <= right)) (PreH14 : (right <= UINT_MAX)) (PreH15 : (dest < 63)) (PreH16 : (current_tcb <> 0)) (PreH17 : (0 <= current_prio)) (PreH18 : (current_prio < 64)) (PreH19 : (current_prio <> dest)) (PreH20 : (current_space <> target)) (PreH21 : (current_space <> 0)) (PreH22 : (class <= 16)) (PreH23 : (target <> 0)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) <> 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ”
  &&  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
.

Definition grant_cspace_cap_partial_solve_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((Z.land grant_right 64) <> 0)) (PreH2 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH3 : (current_space <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (destTask_Prio_pre = dest)) (PreH6 : (cap_Class_pre = class)) (PreH7 : (cap_Right_pre = right)) (PreH8 : (0 <= dest)) (PreH9 : (dest <= 255)) (PreH10 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH11 : (0 <= class)) (PreH12 : (class <= UINT_MAX)) (PreH13 : (0 <= right)) (PreH14 : (right <= UINT_MAX)) (PreH15 : (dest < 63)) (PreH16 : (current_tcb <> 0)) (PreH17 : (0 <= current_prio)) (PreH18 : (current_prio < 64)) (PreH19 : (current_prio <> dest)) (PreH20 : (current_space <> target)) (PreH21 : (current_space <> 0)) (PreH22 : (class > 16)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) <> 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class > 16) ”
  &&  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
.

Definition grant_cspace_cap_partial_solve_wit_4_callee_null_pure := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (current_space <> 0)) (PreH3 : (destTask_Prio_pre < 63)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (dest < 63)) (PreH15 : (current_tcb <> 0)) (PreH16 : (0 <= current_prio)) (PreH17 : (current_prio < 64)) (PreH18 : (current_prio <> dest)) (PreH19 : (current_space <> target)) (PreH20 : (current_space <> 0)) (PreH21 : (class <= 16)) (PreH22 : (target = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= 16) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target = 0) ”
.

Definition grant_cspace_cap_partial_solve_wit_4_callee_null_aux := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (current_space <> 0)) (PreH3 : (destTask_Prio_pre < 63)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (dest < 63)) (PreH15 : (current_tcb <> 0)) (PreH16 : (0 <= current_prio)) (PreH17 : (current_prio < 64)) (PreH18 : (current_prio <> dest)) (PreH19 : (current_space <> target)) (PreH20 : (current_space <> 0)) (PreH21 : (class <= 16)) (PreH22 : (target = 0)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= 16) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target = 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_partial_solve_wit_4_callee_null := grant_cspace_cap_partial_solve_wit_4_callee_null_pure -> grant_cspace_cap_partial_solve_wit_4_callee_null_aux.

Definition grant_cspace_cap_partial_solve_wit_5_callee_success_pure := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (current_space <> 0)) (PreH3 : (destTask_Prio_pre < 63)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (dest < 63)) (PreH15 : (current_tcb <> 0)) (PreH16 : (0 <= current_prio)) (PreH17 : (current_prio < 64)) (PreH18 : (current_prio <> dest)) (PreH19 : (current_space <> target)) (PreH20 : (current_space <> 0)) (PreH21 : (class <= 16)) (PreH22 : (target <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= 16) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target <> 0) ”
.

Definition grant_cspace_cap_partial_solve_wit_5_callee_success_aux := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (current_space <> 0)) (PreH3 : (destTask_Prio_pre < 63)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (dest < 63)) (PreH15 : (current_tcb <> 0)) (PreH16 : (0 <= current_prio)) (PreH17 : (current_prio < 64)) (PreH18 : (current_prio <> dest)) (PreH19 : (current_space <> target)) (PreH20 : (current_space <> 0)) (PreH21 : (class <= 16)) (PreH22 : (target <> 0)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= 16) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target <> 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_partial_solve_wit_5_callee_success := grant_cspace_cap_partial_solve_wit_5_callee_success_pure -> grant_cspace_cap_partial_solve_wit_5_callee_success_aux.

Definition grant_cspace_cap_partial_solve_wit_6_callee_invalid_pure := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (current_space <> 0)) (PreH3 : (destTask_Prio_pre < 63)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (dest < 63)) (PreH15 : (current_tcb <> 0)) (PreH16 : (0 <= current_prio)) (PreH17 : (current_prio < 64)) (PreH18 : (current_prio <> dest)) (PreH19 : (current_space <> target)) (PreH20 : (current_space <> 0)) (PreH21 : (class > 16)) ,
  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (class > 16) ”
.

Definition grant_cspace_cap_partial_solve_wit_6_callee_invalid_aux := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (current_space <> 0)) (PreH3 : (destTask_Prio_pre < 63)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (dest < 63)) (PreH15 : (current_tcb <> 0)) (PreH16 : (0 <= current_prio)) (PreH17 : (current_prio < 64)) (PreH18 : (current_prio <> dest)) (PreH19 : (current_space <> target)) (PreH20 : (current_space <> 0)) (PreH21 : (class > 16)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (class > 16) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class > 16) ”
  &&  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "CapParent" ) ) + (dest * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_partial_solve_wit_6_callee_invalid := grant_cspace_cap_partial_solve_wit_6_callee_invalid_pure -> grant_cspace_cap_partial_solve_wit_6_callee_invalid_aux.

Definition grant_cspace_cap_partial_solve_wit_7_callee_null_pure := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent = current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target = 0)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= 16) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target = 0) ”
.

Definition grant_cspace_cap_partial_solve_wit_7_callee_null_aux := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent = current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target = 0)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= 16) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target = 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) <> 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
.

Definition grant_cspace_cap_partial_solve_wit_7_callee_null := grant_cspace_cap_partial_solve_wit_7_callee_null_pure -> grant_cspace_cap_partial_solve_wit_7_callee_null_aux.

Definition grant_cspace_cap_partial_solve_wit_8_callee_success_pure := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent = current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target <> 0)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= 16) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target <> 0) ”
.

Definition grant_cspace_cap_partial_solve_wit_8_callee_success_aux := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent = current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target <> 0)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= 16) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target <> 0) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) <> 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class <= 16) ” 
  &&  “ (target <> 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
.

Definition grant_cspace_cap_partial_solve_wit_8_callee_success := grant_cspace_cap_partial_solve_wit_8_callee_success_pure -> grant_cspace_cap_partial_solve_wit_8_callee_success_aux.

Definition grant_cspace_cap_partial_solve_wit_9_callee_invalid_pure := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent = current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class > 16)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> current_space)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (class > 16) ”
.

Definition grant_cspace_cap_partial_solve_wit_9_callee_invalid_aux := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (parent = current_prio)) (PreH2 : ((Z.land grant_right 64) <> 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class > 16)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
|--
  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (class > 16) ” 
  &&  “ (parent = current_prio) ” 
  &&  “ ((Z.land grant_right 64) <> 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) <> 0) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (destTask_Prio_pre = dest) ” 
  &&  “ (cap_Class_pre = class) ” 
  &&  “ (cap_Right_pre = right) ” 
  &&  “ (0 <= dest) ” 
  &&  “ (dest <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) = dest) ” 
  &&  “ (0 <= class) ” 
  &&  “ (class <= UINT_MAX) ” 
  &&  “ (0 <= right) ” 
  &&  “ (right <= UINT_MAX) ” 
  &&  “ (dest < 63) ” 
  &&  “ (current_tcb <> 0) ” 
  &&  “ (0 <= current_prio) ” 
  &&  “ (current_prio < 64) ” 
  &&  “ (current_prio <> dest) ” 
  &&  “ (current_space <> target) ” 
  &&  “ (current_space <> 0) ” 
  &&  “ (class > 16) ”
  &&  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current_tcb)
  **  ((&((current_tcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> current_prio)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (current_prio * sizeof(PTR)))) # Ptr  |-> current_space)
  **  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  ((&(((&((current_space)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> grant_right)
.

Definition grant_cspace_cap_partial_solve_wit_9_callee_invalid := grant_cspace_cap_partial_solve_wit_9_callee_invalid_pure -> grant_cspace_cap_partial_solve_wit_9_callee_invalid_aux.

Module Type VC_Correct.


Axiom proof_of_grant_cspace_cap_safety_wit_1 : grant_cspace_cap_safety_wit_1.
Axiom proof_of_grant_cspace_cap_safety_wit_2 : grant_cspace_cap_safety_wit_2.
Axiom proof_of_grant_cspace_cap_safety_wit_3 : grant_cspace_cap_safety_wit_3.
Axiom proof_of_grant_cspace_cap_safety_wit_4 : grant_cspace_cap_safety_wit_4.
Axiom proof_of_grant_cspace_cap_safety_wit_5 : grant_cspace_cap_safety_wit_5.
Axiom proof_of_grant_cspace_cap_safety_wit_6 : grant_cspace_cap_safety_wit_6.
Axiom proof_of_grant_cspace_cap_safety_wit_7 : grant_cspace_cap_safety_wit_7.
Axiom proof_of_grant_cspace_cap_safety_wit_8 : grant_cspace_cap_safety_wit_8.
Axiom proof_of_grant_cspace_cap_safety_wit_9 : grant_cspace_cap_safety_wit_9.
Axiom proof_of_grant_cspace_cap_safety_wit_10 : grant_cspace_cap_safety_wit_10.
Axiom proof_of_grant_cspace_cap_safety_wit_11 : grant_cspace_cap_safety_wit_11.
Axiom proof_of_grant_cspace_cap_safety_wit_12 : grant_cspace_cap_safety_wit_12.
Axiom proof_of_grant_cspace_cap_safety_wit_13 : grant_cspace_cap_safety_wit_13.
Axiom proof_of_grant_cspace_cap_safety_wit_14_callee_null : grant_cspace_cap_safety_wit_14_callee_null.
Axiom proof_of_grant_cspace_cap_safety_wit_15_callee_success : grant_cspace_cap_safety_wit_15_callee_success.
Axiom proof_of_grant_cspace_cap_safety_wit_16_callee_invalid : grant_cspace_cap_safety_wit_16_callee_invalid.
Axiom proof_of_grant_cspace_cap_safety_wit_17_callee_null : grant_cspace_cap_safety_wit_17_callee_null.
Axiom proof_of_grant_cspace_cap_safety_wit_18_callee_success : grant_cspace_cap_safety_wit_18_callee_success.
Axiom proof_of_grant_cspace_cap_safety_wit_19_callee_invalid : grant_cspace_cap_safety_wit_19_callee_invalid.
Axiom proof_of_grant_cspace_cap_return_wit_1 : grant_cspace_cap_return_wit_1.
Axiom proof_of_grant_cspace_cap_return_wit_2 : grant_cspace_cap_return_wit_2.
Axiom proof_of_grant_cspace_cap_return_wit_3 : grant_cspace_cap_return_wit_3.
Axiom proof_of_grant_cspace_cap_return_wit_4 : grant_cspace_cap_return_wit_4.
Axiom proof_of_grant_cspace_cap_return_wit_5 : grant_cspace_cap_return_wit_5.
Axiom proof_of_grant_cspace_cap_return_wit_6 : grant_cspace_cap_return_wit_6.
Axiom proof_of_grant_cspace_cap_return_wit_7_callee_null : grant_cspace_cap_return_wit_7_callee_null.
Axiom proof_of_grant_cspace_cap_return_wit_8_callee_invalid : grant_cspace_cap_return_wit_8_callee_invalid.
Axiom proof_of_grant_cspace_cap_return_wit_9_callee_null : grant_cspace_cap_return_wit_9_callee_null.
Axiom proof_of_grant_cspace_cap_return_wit_10_callee_invalid : grant_cspace_cap_return_wit_10_callee_invalid.
Axiom proof_of_grant_cspace_cap_return_wit_11_callee_success : grant_cspace_cap_return_wit_11_callee_success.
Axiom proof_of_grant_cspace_cap_return_wit_12_callee_success : grant_cspace_cap_return_wit_12_callee_success.
Axiom proof_of_grant_cspace_cap_return_wit_13 : grant_cspace_cap_return_wit_13.
Axiom proof_of_grant_cspace_cap_return_wit_14 : grant_cspace_cap_return_wit_14.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_1 : grant_cspace_cap_partial_solve_wit_1.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_2 : grant_cspace_cap_partial_solve_wit_2.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_3 : grant_cspace_cap_partial_solve_wit_3.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_4_callee_null_pure : grant_cspace_cap_partial_solve_wit_4_callee_null_pure.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_4_callee_null : grant_cspace_cap_partial_solve_wit_4_callee_null.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_5_callee_success_pure : grant_cspace_cap_partial_solve_wit_5_callee_success_pure.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_5_callee_success : grant_cspace_cap_partial_solve_wit_5_callee_success.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_6_callee_invalid_pure : grant_cspace_cap_partial_solve_wit_6_callee_invalid_pure.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_6_callee_invalid : grant_cspace_cap_partial_solve_wit_6_callee_invalid.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_7_callee_null_pure : grant_cspace_cap_partial_solve_wit_7_callee_null_pure.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_7_callee_null : grant_cspace_cap_partial_solve_wit_7_callee_null.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_8_callee_success_pure : grant_cspace_cap_partial_solve_wit_8_callee_success_pure.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_8_callee_success : grant_cspace_cap_partial_solve_wit_8_callee_success.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_9_callee_invalid_pure : grant_cspace_cap_partial_solve_wit_9_callee_invalid_pure.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_9_callee_invalid : grant_cspace_cap_partial_solve_wit_9_callee_invalid.

End VC_Correct.
