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
Local Open Scope sac.

(*----- Function ucos_Grant_Cap -----*)

Definition ucos_Grant_Cap_safety_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (class > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (dest) (32)) >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (class <= 16)) (PreH13 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH14 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (destTask_Prio_pre = dest)) (PreH3 : (cap_Class_pre = class)) (PreH4 : (cap_Right_pre = right)) (PreH5 : (0 <= dest)) (PreH6 : (dest <= 255)) (PreH7 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH8 : (0 <= class)) (PreH9 : (class <= UINT_MAX)) (PreH10 : (0 <= right)) (PreH11 : (right <= UINT_MAX)) (PreH12 : (class <= 16)) (PreH13 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH14 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (class <= 16)) (PreH14 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH15 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (class <= 16)) (PreH14 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH15 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_7 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (class > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest) (32)) >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (class <= 16)) (PreH15 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH16 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (class <= 16)) (PreH15 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH16 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_11 := 
forall (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (class <= 16)) (PreH2 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH3 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_12 := 
forall (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (class <= 16)) (PreH2 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH3 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_13 := 
forall (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (target = 0)) (PreH2 : (class <= 16)) (PreH3 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH4 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_14 := 
forall (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (target <> 0)) (PreH2 : (class <= 16)) (PreH3 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH4 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_entail_wit_1_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (class <= 16)) (PreH15 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH16 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (class <= 16) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
.

Definition ucos_Grant_Cap_entail_wit_1_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : (class <= 16)) (PreH15 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH16 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (class <= 16) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
.

Definition ucos_Grant_Cap_return_wit_1 := 
forall (old_right: Z) (right: Z) (class: Z) (dest: Z) (target: Z) (PreH1 : (target <> 0)) (PreH2 : (class <= 16)) (PreH3 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH4 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
|--
  “ (0 = 0) ” 
  &&  “ (class <= 16) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target <> 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
.

Definition ucos_Grant_Cap_return_wit_2 := 
forall (class: Z) (dest: Z) (target: Z) (PreH1 : (target = 0)) (PreH2 : (class <= 16)) (PreH3 : ((unsigned_last_nbits (dest) (32)) < 64)) (PreH4 : (target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (11 = 11) ” 
  &&  “ (class <= 16) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) < 64) ” 
  &&  “ (target = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_Grant_Cap_return_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest)) (PreH5 : (cap_Class_pre = class)) (PreH6 : (cap_Right_pre = right)) (PreH7 : (0 <= dest)) (PreH8 : (dest <= 255)) (PreH9 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH10 : (0 <= class)) (PreH11 : (class <= UINT_MAX)) (PreH12 : (0 <= right)) (PreH13 : (right <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest) (32)) >= 64)) ,
  TT && emp 
|--
  “ (11 = 11) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) >= 64) ”
  &&  emp
.

Definition ucos_Grant_Cap_return_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : (class > 16)) ,
  TT && emp 
|--
  (“ (11 = 11) ” 
  &&  “ (class > 16) ”
  &&  emp)
  ||
  (“ (11 = 11) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) >= 64) ”
  &&  emp)
.

Definition ucos_Grant_Cap_return_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (class: Z) (dest: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest)) (PreH4 : (cap_Class_pre = class)) (PreH5 : (cap_Right_pre = right)) (PreH6 : (0 <= dest)) (PreH7 : (dest <= 255)) (PreH8 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH9 : (0 <= class)) (PreH10 : (class <= UINT_MAX)) (PreH11 : (0 <= right)) (PreH12 : (right <= UINT_MAX)) (PreH13 : ((unsigned_last_nbits (dest) (32)) >= 64)) ,
  TT && emp 
|--
  (“ (11 = 11) ” 
  &&  “ (class > 16) ”
  &&  emp)
  ||
  (“ (11 = 11) ” 
  &&  “ ((unsigned_last_nbits (dest) (32)) >= 64) ”
  &&  emp)
.

Module Type VC_Correct.


Axiom proof_of_ucos_Grant_Cap_safety_wit_1 : ucos_Grant_Cap_safety_wit_1.
Axiom proof_of_ucos_Grant_Cap_safety_wit_2 : ucos_Grant_Cap_safety_wit_2.
Axiom proof_of_ucos_Grant_Cap_safety_wit_3 : ucos_Grant_Cap_safety_wit_3.
Axiom proof_of_ucos_Grant_Cap_safety_wit_4 : ucos_Grant_Cap_safety_wit_4.
Axiom proof_of_ucos_Grant_Cap_safety_wit_5 : ucos_Grant_Cap_safety_wit_5.
Axiom proof_of_ucos_Grant_Cap_safety_wit_6 : ucos_Grant_Cap_safety_wit_6.
Axiom proof_of_ucos_Grant_Cap_safety_wit_7 : ucos_Grant_Cap_safety_wit_7.
Axiom proof_of_ucos_Grant_Cap_safety_wit_8 : ucos_Grant_Cap_safety_wit_8.
Axiom proof_of_ucos_Grant_Cap_safety_wit_9 : ucos_Grant_Cap_safety_wit_9.
Axiom proof_of_ucos_Grant_Cap_safety_wit_10 : ucos_Grant_Cap_safety_wit_10.
Axiom proof_of_ucos_Grant_Cap_safety_wit_11 : ucos_Grant_Cap_safety_wit_11.
Axiom proof_of_ucos_Grant_Cap_safety_wit_12 : ucos_Grant_Cap_safety_wit_12.
Axiom proof_of_ucos_Grant_Cap_safety_wit_13 : ucos_Grant_Cap_safety_wit_13.
Axiom proof_of_ucos_Grant_Cap_safety_wit_14 : ucos_Grant_Cap_safety_wit_14.
Axiom proof_of_ucos_Grant_Cap_entail_wit_1_1 : ucos_Grant_Cap_entail_wit_1_1.
Axiom proof_of_ucos_Grant_Cap_entail_wit_1_2 : ucos_Grant_Cap_entail_wit_1_2.
Axiom proof_of_ucos_Grant_Cap_return_wit_1 : ucos_Grant_Cap_return_wit_1.
Axiom proof_of_ucos_Grant_Cap_return_wit_2 : ucos_Grant_Cap_return_wit_2.
Axiom proof_of_ucos_Grant_Cap_return_wit_3 : ucos_Grant_Cap_return_wit_3.
Axiom proof_of_ucos_Grant_Cap_return_wit_4 : ucos_Grant_Cap_return_wit_4.
Axiom proof_of_ucos_Grant_Cap_return_wit_5 : ucos_Grant_Cap_return_wit_5.

End VC_Correct.
