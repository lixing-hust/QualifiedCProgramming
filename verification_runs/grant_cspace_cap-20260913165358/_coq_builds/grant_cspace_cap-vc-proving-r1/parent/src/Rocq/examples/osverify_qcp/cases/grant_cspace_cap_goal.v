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

Definition ucos_Grant_Cap_safety_wit_1_class_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_class_invalid: Z) (class_class_invalid: Z) (dest_class_invalid: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (destTask_Prio_pre = dest_class_invalid)) (PreH3 : (cap_Class_pre = class_class_invalid)) (PreH4 : (cap_Right_pre = right_class_invalid)) (PreH5 : (0 <= dest_class_invalid)) (PreH6 : (dest_class_invalid <= 255)) (PreH7 : ((unsigned_last_nbits (dest_class_invalid) (32)) = dest_class_invalid)) (PreH8 : (0 <= class_class_invalid)) (PreH9 : (class_class_invalid <= UINT_MAX)) (PreH10 : (0 <= right_class_invalid)) (PreH11 : (right_class_invalid <= UINT_MAX)) (PreH12 : (class_class_invalid > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_2_prio_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_prio_invalid: Z) (class_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (destTask_Prio_pre = dest_prio_invalid)) (PreH3 : (cap_Class_pre = class_prio_invalid)) (PreH4 : (cap_Right_pre = right_prio_invalid)) (PreH5 : (0 <= dest_prio_invalid)) (PreH6 : (dest_prio_invalid <= 255)) (PreH7 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH8 : (0 <= class_prio_invalid)) (PreH9 : (class_prio_invalid <= 16)) (PreH10 : (0 <= right_prio_invalid)) (PreH11 : (right_prio_invalid <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (dest_prio_invalid) (32)) >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_3_null_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_null_target: Z) (class_null_target: Z) (dest_null_target: Z) (target_null_target: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (destTask_Prio_pre = dest_null_target)) (PreH3 : (cap_Class_pre = class_null_target)) (PreH4 : (cap_Right_pre = right_null_target)) (PreH5 : (0 <= dest_null_target)) (PreH6 : (dest_null_target <= 255)) (PreH7 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH8 : (0 <= class_null_target)) (PreH9 : (class_null_target <= 16)) (PreH10 : (0 <= right_null_target)) (PreH11 : (right_null_target <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (dest_null_target) (32)) < 64)) (PreH13 : (target_null_target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> target_null_target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_4_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (destTask_Prio_pre = dest_valid_target)) (PreH3 : (cap_Class_pre = class_valid_target)) (PreH4 : (cap_Right_pre = right_valid_target)) (PreH5 : (0 <= dest_valid_target)) (PreH6 : (dest_valid_target <= 255)) (PreH7 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH8 : (0 <= class_valid_target)) (PreH9 : (class_valid_target <= 16)) (PreH10 : (0 <= right_valid_target)) (PreH11 : (right_valid_target <= UINT_MAX)) (PreH12 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH13 : (target_valid_target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_5_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest_valid_target)) (PreH4 : (cap_Class_pre = class_valid_target)) (PreH5 : (cap_Right_pre = right_valid_target)) (PreH6 : (0 <= dest_valid_target)) (PreH7 : (dest_valid_target <= 255)) (PreH8 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH9 : (0 <= class_valid_target)) (PreH10 : (class_valid_target <= 16)) (PreH11 : (0 <= right_valid_target)) (PreH12 : (right_valid_target <= UINT_MAX)) (PreH13 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH14 : (target_valid_target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_6_null_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_null_target: Z) (class_null_target: Z) (dest_null_target: Z) (target_null_target: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest_null_target)) (PreH4 : (cap_Class_pre = class_null_target)) (PreH5 : (cap_Right_pre = right_null_target)) (PreH6 : (0 <= dest_null_target)) (PreH7 : (dest_null_target <= 255)) (PreH8 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH9 : (0 <= class_null_target)) (PreH10 : (class_null_target <= 16)) (PreH11 : (0 <= right_null_target)) (PreH12 : (right_null_target <= UINT_MAX)) (PreH13 : ((unsigned_last_nbits (dest_null_target) (32)) < 64)) (PreH14 : (target_null_target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> target_null_target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_7_prio_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_prio_invalid: Z) (class_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest_prio_invalid)) (PreH4 : (cap_Class_pre = class_prio_invalid)) (PreH5 : (cap_Right_pre = right_prio_invalid)) (PreH6 : (0 <= dest_prio_invalid)) (PreH7 : (dest_prio_invalid <= 255)) (PreH8 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH9 : (0 <= class_prio_invalid)) (PreH10 : (class_prio_invalid <= 16)) (PreH11 : (0 <= right_prio_invalid)) (PreH12 : (right_prio_invalid <= UINT_MAX)) (PreH13 : ((unsigned_last_nbits (dest_prio_invalid) (32)) >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_8_class_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_class_invalid: Z) (class_class_invalid: Z) (dest_class_invalid: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest_class_invalid)) (PreH4 : (cap_Class_pre = class_class_invalid)) (PreH5 : (cap_Right_pre = right_class_invalid)) (PreH6 : (0 <= dest_class_invalid)) (PreH7 : (dest_class_invalid <= 255)) (PreH8 : ((unsigned_last_nbits (dest_class_invalid) (32)) = dest_class_invalid)) (PreH9 : (0 <= class_class_invalid)) (PreH10 : (class_class_invalid <= UINT_MAX)) (PreH11 : (0 <= right_class_invalid)) (PreH12 : (right_class_invalid <= UINT_MAX)) (PreH13 : (class_class_invalid > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_9_prio_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_prio_invalid: Z) (class_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_prio_invalid)) (PreH5 : (cap_Class_pre = class_prio_invalid)) (PreH6 : (cap_Right_pre = right_prio_invalid)) (PreH7 : (0 <= dest_prio_invalid)) (PreH8 : (dest_prio_invalid <= 255)) (PreH9 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH10 : (0 <= class_prio_invalid)) (PreH11 : (class_prio_invalid <= 16)) (PreH12 : (0 <= right_prio_invalid)) (PreH13 : (right_prio_invalid <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_prio_invalid) (32)) >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_10_null_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_null_target: Z) (class_null_target: Z) (dest_null_target: Z) (target_null_target: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_null_target)) (PreH5 : (cap_Class_pre = class_null_target)) (PreH6 : (cap_Right_pre = right_null_target)) (PreH7 : (0 <= dest_null_target)) (PreH8 : (dest_null_target <= 255)) (PreH9 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH10 : (0 <= class_null_target)) (PreH11 : (class_null_target <= 16)) (PreH12 : (0 <= right_null_target)) (PreH13 : (right_null_target <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_null_target) (32)) < 64)) (PreH15 : (target_null_target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> target_null_target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_11_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_valid_target)) (PreH5 : (cap_Class_pre = class_valid_target)) (PreH6 : (cap_Right_pre = right_valid_target)) (PreH7 : (0 <= dest_valid_target)) (PreH8 : (dest_valid_target <= 255)) (PreH9 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH10 : (0 <= class_valid_target)) (PreH11 : (class_valid_target <= 16)) (PreH12 : (0 <= right_valid_target)) (PreH13 : (right_valid_target <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH15 : (target_valid_target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_12_null_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_null_target: Z) (class_null_target: Z) (dest_null_target: Z) (target_null_target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_null_target)) (PreH5 : (cap_Class_pre = class_null_target)) (PreH6 : (cap_Right_pre = right_null_target)) (PreH7 : (0 <= dest_null_target)) (PreH8 : (dest_null_target <= 255)) (PreH9 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH10 : (0 <= class_null_target)) (PreH11 : (class_null_target <= 16)) (PreH12 : (0 <= right_null_target)) (PreH13 : (right_null_target <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_null_target) (32)) < 64)) (PreH15 : (target_null_target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_13_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_valid_target)) (PreH5 : (cap_Class_pre = class_valid_target)) (PreH6 : (cap_Right_pre = right_valid_target)) (PreH7 : (0 <= dest_valid_target)) (PreH8 : (dest_valid_target <= 255)) (PreH9 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH10 : (0 <= class_valid_target)) (PreH11 : (class_valid_target <= 16)) (PreH12 : (0 <= right_valid_target)) (PreH13 : (right_valid_target <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH15 : (target_valid_target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_14_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (target_valid_target = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (destTask_Prio_pre = dest_valid_target)) (PreH6 : (cap_Class_pre = class_valid_target)) (PreH7 : (cap_Right_pre = right_valid_target)) (PreH8 : (0 <= dest_valid_target)) (PreH9 : (dest_valid_target <= 255)) (PreH10 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH11 : (0 <= class_valid_target)) (PreH12 : (class_valid_target <= 16)) (PreH13 : (0 <= right_valid_target)) (PreH14 : (right_valid_target <= UINT_MAX)) (PreH15 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH16 : (target_valid_target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_return_wit_1_valid_target := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (target_valid_target <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (destTask_Prio_pre = dest_valid_target)) (PreH6 : (cap_Class_pre = class_valid_target)) (PreH7 : (cap_Right_pre = right_valid_target)) (PreH8 : (0 <= dest_valid_target)) (PreH9 : (dest_valid_target <= 255)) (PreH10 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH11 : (0 <= class_valid_target)) (PreH12 : (class_valid_target <= 16)) (PreH13 : (0 <= right_valid_target)) (PreH14 : (right_valid_target <= UINT_MAX)) (PreH15 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH16 : (target_valid_target <> 0)) ,
  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre))
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
|--
  “ (0 = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) right_valid_target))
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (1 <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : ((Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) <= UINT_MAX)) (PreH4 : (1 >= 0)) (PreH5 : (cap_Class_pre >= 0)) (PreH6 : ((Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) >= 0)) (PreH7 : (target_valid_target <> 0)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (cap_Class_pre <= 16)) (PreH10 : (0 <= cap_Class_pre)) (PreH11 : (destTask_Prio_pre = dest_valid_target)) (PreH12 : (cap_Class_pre = class_valid_target)) (PreH13 : (cap_Right_pre = right_valid_target)) (PreH14 : (0 <= dest_valid_target)) (PreH15 : (dest_valid_target <= 255)) (PreH16 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH17 : (0 <= class_valid_target)) (PreH18 : (class_valid_target <= 16)) (PreH19 : (0 <= right_valid_target)) (PreH20 : (right_valid_target <= UINT_MAX)) (PreH21 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH22 : (target_valid_target <> 0)) ,
  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre))
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
|--
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) right_valid_target))
).

Definition ucos_Grant_Cap_return_wit_1_valid_target_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (1 <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : ((Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) <= UINT_MAX)) (PreH4 : (1 >= 0)) (PreH5 : (cap_Class_pre >= 0)) (PreH6 : ((Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) >= 0)) (PreH7 : (target_valid_target <> 0)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (cap_Class_pre <= 16)) (PreH10 : (0 <= cap_Class_pre)) (PreH11 : (destTask_Prio_pre = dest_valid_target)) (PreH12 : (cap_Class_pre = class_valid_target)) (PreH13 : (cap_Right_pre = right_valid_target)) (PreH14 : (0 <= dest_valid_target)) (PreH15 : (dest_valid_target <= 255)) (PreH16 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH17 : (0 <= class_valid_target)) (PreH18 : (class_valid_target <= 16)) (PreH19 : (0 <= right_valid_target)) (PreH20 : (right_valid_target <= UINT_MAX)) (PreH21 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH22 : (target_valid_target <> 0)) ,
  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre))
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
|--
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) right_valid_target))
.

Definition ucos_Grant_Cap_return_wit_2_null_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_null_target: Z) (class_null_target: Z) (dest_null_target: Z) (target_null_target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_null_target)) (PreH5 : (cap_Class_pre = class_null_target)) (PreH6 : (cap_Right_pre = right_null_target)) (PreH7 : (0 <= dest_null_target)) (PreH8 : (dest_null_target <= 255)) (PreH9 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH10 : (0 <= class_null_target)) (PreH11 : (class_null_target <= 16)) (PreH12 : (0 <= right_null_target)) (PreH13 : (right_null_target <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_null_target) (32)) < 64)) (PreH15 : (target_null_target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
|--
  “ (11 = 11) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_Grant_Cap_return_wit_3_prio_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_prio_invalid: Z) (class_prio_invalid: Z) (dest_prio_invalid: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_prio_invalid)) (PreH5 : (cap_Class_pre = class_prio_invalid)) (PreH6 : (cap_Right_pre = right_prio_invalid)) (PreH7 : (0 <= dest_prio_invalid)) (PreH8 : (dest_prio_invalid <= 255)) (PreH9 : ((unsigned_last_nbits (dest_prio_invalid) (32)) = dest_prio_invalid)) (PreH10 : (0 <= class_prio_invalid)) (PreH11 : (class_prio_invalid <= 16)) (PreH12 : (0 <= right_prio_invalid)) (PreH13 : (right_prio_invalid <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_prio_invalid) (32)) >= 64)) ,
  TT && emp 
|--
  “ (11 = 11) ”
  &&  emp
.

Definition ucos_Grant_Cap_return_wit_4_class_invalid := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_class_invalid: Z) (class_class_invalid: Z) (dest_class_invalid: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (destTask_Prio_pre = dest_class_invalid)) (PreH4 : (cap_Class_pre = class_class_invalid)) (PreH5 : (cap_Right_pre = right_class_invalid)) (PreH6 : (0 <= dest_class_invalid)) (PreH7 : (dest_class_invalid <= 255)) (PreH8 : ((unsigned_last_nbits (dest_class_invalid) (32)) = dest_class_invalid)) (PreH9 : (0 <= class_class_invalid)) (PreH10 : (class_class_invalid <= UINT_MAX)) (PreH11 : (0 <= right_class_invalid)) (PreH12 : (right_class_invalid <= UINT_MAX)) (PreH13 : (class_class_invalid > 16)) ,
  TT && emp 
|--
  “ (11 = 11) ”
  &&  emp
.

Definition ucos_Grant_Cap_partial_solve_wit_1_null_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right_null_target: Z) (class_null_target: Z) (dest_null_target: Z) (target_null_target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_null_target)) (PreH5 : (cap_Class_pre = class_null_target)) (PreH6 : (cap_Right_pre = right_null_target)) (PreH7 : (0 <= dest_null_target)) (PreH8 : (dest_null_target <= 255)) (PreH9 : ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target)) (PreH10 : (0 <= class_null_target)) (PreH11 : (class_null_target <= 16)) (PreH12 : (0 <= right_null_target)) (PreH13 : (right_null_target <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_null_target) (32)) < 64)) (PreH15 : (target_null_target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_null_target * sizeof(PTR)))) # Ptr  |-> target_null_target)
|--
  “ (destTask_Prio_pre < 64) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (0 <= cap_Class_pre) ” 
  &&  “ (destTask_Prio_pre = dest_null_target) ” 
  &&  “ (cap_Class_pre = class_null_target) ” 
  &&  “ (cap_Right_pre = right_null_target) ” 
  &&  “ (0 <= dest_null_target) ” 
  &&  “ (dest_null_target <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest_null_target) (32)) = dest_null_target) ” 
  &&  “ (0 <= class_null_target) ” 
  &&  “ (class_null_target <= 16) ” 
  &&  “ (0 <= right_null_target) ” 
  &&  “ (right_null_target <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest_null_target) (32)) < 64) ” 
  &&  “ (target_null_target = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0)
.

Definition ucos_Grant_Cap_partial_solve_wit_2_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (destTask_Prio_pre = dest_valid_target)) (PreH5 : (cap_Class_pre = class_valid_target)) (PreH6 : (cap_Right_pre = right_valid_target)) (PreH7 : (0 <= dest_valid_target)) (PreH8 : (dest_valid_target <= 255)) (PreH9 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH10 : (0 <= class_valid_target)) (PreH11 : (class_valid_target <= 16)) (PreH12 : (0 <= right_valid_target)) (PreH13 : (right_valid_target <= UINT_MAX)) (PreH14 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH15 : (target_valid_target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ (destTask_Prio_pre < 64) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (0 <= cap_Class_pre) ” 
  &&  “ (destTask_Prio_pre = dest_valid_target) ” 
  &&  “ (cap_Class_pre = class_valid_target) ” 
  &&  “ (cap_Right_pre = right_valid_target) ” 
  &&  “ (0 <= dest_valid_target) ” 
  &&  “ (dest_valid_target <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target) ” 
  &&  “ (0 <= class_valid_target) ” 
  &&  “ (class_valid_target <= 16) ” 
  &&  “ (0 <= right_valid_target) ” 
  &&  “ (right_valid_target <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest_valid_target) (32)) < 64) ” 
  &&  “ (target_valid_target <> 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
.

Definition ucos_Grant_Cap_partial_solve_wit_3_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (target_valid_target <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (destTask_Prio_pre = dest_valid_target)) (PreH6 : (cap_Class_pre = class_valid_target)) (PreH7 : (cap_Right_pre = right_valid_target)) (PreH8 : (0 <= dest_valid_target)) (PreH9 : (dest_valid_target <= 255)) (PreH10 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH11 : (0 <= class_valid_target)) (PreH12 : (class_valid_target <= 16)) (PreH13 : (0 <= right_valid_target)) (PreH14 : (right_valid_target <= UINT_MAX)) (PreH15 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH16 : (target_valid_target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ (target_valid_target <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (0 <= cap_Class_pre) ” 
  &&  “ (destTask_Prio_pre = dest_valid_target) ” 
  &&  “ (cap_Class_pre = class_valid_target) ” 
  &&  “ (cap_Right_pre = right_valid_target) ” 
  &&  “ (0 <= dest_valid_target) ” 
  &&  “ (dest_valid_target <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target) ” 
  &&  “ (0 <= class_valid_target) ” 
  &&  “ (class_valid_target <= 16) ” 
  &&  “ (0 <= right_valid_target) ” 
  &&  “ (right_valid_target <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest_valid_target) (32)) < 64) ” 
  &&  “ (target_valid_target <> 0) ”
  &&  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
.

Definition ucos_Grant_Cap_partial_solve_wit_4_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (target_valid_target <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (destTask_Prio_pre = dest_valid_target)) (PreH6 : (cap_Class_pre = class_valid_target)) (PreH7 : (cap_Right_pre = right_valid_target)) (PreH8 : (0 <= dest_valid_target)) (PreH9 : (dest_valid_target <= 255)) (PreH10 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH11 : (0 <= class_valid_target)) (PreH12 : (class_valid_target <= 16)) (PreH13 : (0 <= right_valid_target)) (PreH14 : (right_valid_target <= UINT_MAX)) (PreH15 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH16 : (target_valid_target <> 0)) ,
  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ (target_valid_target <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (0 <= cap_Class_pre) ” 
  &&  “ (destTask_Prio_pre = dest_valid_target) ” 
  &&  “ (cap_Class_pre = class_valid_target) ” 
  &&  “ (cap_Right_pre = right_valid_target) ” 
  &&  “ (0 <= dest_valid_target) ” 
  &&  “ (dest_valid_target <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target) ” 
  &&  “ (0 <= class_valid_target) ” 
  &&  “ (class_valid_target <= 16) ” 
  &&  “ (0 <= right_valid_target) ” 
  &&  “ (right_valid_target <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest_valid_target) (32)) < 64) ” 
  &&  “ (target_valid_target <> 0) ”
  &&  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
.

Definition ucos_Grant_Cap_partial_solve_wit_5_valid_target := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (target_valid_target <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (destTask_Prio_pre = dest_valid_target)) (PreH6 : (cap_Class_pre = class_valid_target)) (PreH7 : (cap_Right_pre = right_valid_target)) (PreH8 : (0 <= dest_valid_target)) (PreH9 : (dest_valid_target <= 255)) (PreH10 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH11 : (0 <= class_valid_target)) (PreH12 : (class_valid_target <= 16)) (PreH13 : (0 <= right_valid_target)) (PreH14 : (right_valid_target <= UINT_MAX)) (PreH15 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH16 : (target_valid_target <> 0)) ,
  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
|--
  “ (target_valid_target <> 0) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (0 <= cap_Class_pre) ” 
  &&  “ (destTask_Prio_pre = dest_valid_target) ” 
  &&  “ (cap_Class_pre = class_valid_target) ” 
  &&  “ (cap_Right_pre = right_valid_target) ” 
  &&  “ (0 <= dest_valid_target) ” 
  &&  “ (dest_valid_target <= 255) ” 
  &&  “ ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target) ” 
  &&  “ (0 <= class_valid_target) ” 
  &&  “ (class_valid_target <= 16) ” 
  &&  “ (0 <= right_valid_target) ” 
  &&  “ (right_valid_target <= UINT_MAX) ” 
  &&  “ ((unsigned_last_nbits (dest_valid_target) (32)) < 64) ” 
  &&  “ (target_valid_target <> 0) ”
  &&  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
.

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
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target <> 0)) ,
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
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (parent = current_prio)) (PreH4 : ((Z.land grant_right 64) <> 0)) (PreH5 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH6 : (current_space <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (destTask_Prio_pre = dest)) (PreH9 : (cap_Class_pre = class)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (0 <= dest)) (PreH12 : (dest <= 255)) (PreH13 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH14 : (0 <= class)) (PreH15 : (class <= UINT_MAX)) (PreH16 : (0 <= right)) (PreH17 : (right <= UINT_MAX)) (PreH18 : (dest < 63)) (PreH19 : (current_tcb <> 0)) (PreH20 : (0 <= current_prio)) (PreH21 : (current_prio < 64)) (PreH22 : (current_prio <> dest)) (PreH23 : (current_space <> target)) (PreH24 : (current_space <> 0)) (PreH25 : (class <= 16)) (PreH26 : (target <> 0)) ,
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
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH4 : (current_space <> 0)) (PreH5 : (destTask_Prio_pre < 63)) (PreH6 : (destTask_Prio_pre = dest)) (PreH7 : (cap_Class_pre = class)) (PreH8 : (cap_Right_pre = right)) (PreH9 : (0 <= dest)) (PreH10 : (dest <= 255)) (PreH11 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH12 : (0 <= class)) (PreH13 : (class <= UINT_MAX)) (PreH14 : (0 <= right)) (PreH15 : (right <= UINT_MAX)) (PreH16 : (dest < 63)) (PreH17 : (current_tcb <> 0)) (PreH18 : (0 <= current_prio)) (PreH19 : (current_prio < 64)) (PreH20 : (current_prio <> dest)) (PreH21 : (current_space <> target)) (PreH22 : (current_space <> 0)) (PreH23 : (class <= 16)) (PreH24 : (target <> 0)) ,
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
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (target: Z) (grant_right: Z) (parent: Z) (current_space: Z) (running: Z) (current_prio: Z) (current_tcb: Z) (right: Z) (class: Z) (dest: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (parent = current_prio)) (PreH4 : ((Z.land grant_right 64) <> 0)) (PreH5 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH6 : (current_space <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (destTask_Prio_pre = dest)) (PreH9 : (cap_Class_pre = class)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (0 <= dest)) (PreH12 : (dest <= 255)) (PreH13 : ((unsigned_last_nbits (dest) (32)) = dest)) (PreH14 : (0 <= class)) (PreH15 : (class <= UINT_MAX)) (PreH16 : (0 <= right)) (PreH17 : (right <= UINT_MAX)) (PreH18 : (dest < 63)) (PreH19 : (current_tcb <> 0)) (PreH20 : (0 <= current_prio)) (PreH21 : (current_prio < 64)) (PreH22 : (current_prio <> dest)) (PreH23 : (current_space <> target)) (PreH24 : (current_space <> 0)) (PreH25 : (class <= 16)) (PreH26 : (target <> 0)) ,
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


Axiom proof_of_ucos_Grant_Cap_safety_wit_1_class_invalid : ucos_Grant_Cap_safety_wit_1_class_invalid.
Axiom proof_of_ucos_Grant_Cap_safety_wit_2_prio_invalid : ucos_Grant_Cap_safety_wit_2_prio_invalid.
Axiom proof_of_ucos_Grant_Cap_safety_wit_3_null_target : ucos_Grant_Cap_safety_wit_3_null_target.
Axiom proof_of_ucos_Grant_Cap_safety_wit_4_valid_target : ucos_Grant_Cap_safety_wit_4_valid_target.
Axiom proof_of_ucos_Grant_Cap_safety_wit_5_valid_target : ucos_Grant_Cap_safety_wit_5_valid_target.
Axiom proof_of_ucos_Grant_Cap_safety_wit_6_null_target : ucos_Grant_Cap_safety_wit_6_null_target.
Axiom proof_of_ucos_Grant_Cap_safety_wit_7_prio_invalid : ucos_Grant_Cap_safety_wit_7_prio_invalid.
Axiom proof_of_ucos_Grant_Cap_safety_wit_8_class_invalid : ucos_Grant_Cap_safety_wit_8_class_invalid.
Axiom proof_of_ucos_Grant_Cap_safety_wit_9_prio_invalid : ucos_Grant_Cap_safety_wit_9_prio_invalid.
Axiom proof_of_ucos_Grant_Cap_safety_wit_10_null_target : ucos_Grant_Cap_safety_wit_10_null_target.
Axiom proof_of_ucos_Grant_Cap_safety_wit_11_valid_target : ucos_Grant_Cap_safety_wit_11_valid_target.
Axiom proof_of_ucos_Grant_Cap_safety_wit_12_null_target : ucos_Grant_Cap_safety_wit_12_null_target.
Axiom proof_of_ucos_Grant_Cap_safety_wit_13_valid_target : ucos_Grant_Cap_safety_wit_13_valid_target.
Axiom proof_of_ucos_Grant_Cap_safety_wit_14_valid_target : ucos_Grant_Cap_safety_wit_14_valid_target.
Axiom proof_of_ucos_Grant_Cap_return_wit_1_valid_target : ucos_Grant_Cap_return_wit_1_valid_target.
Axiom proof_of_ucos_Grant_Cap_return_wit_2_null_target : ucos_Grant_Cap_return_wit_2_null_target.
Axiom proof_of_ucos_Grant_Cap_return_wit_3_prio_invalid : ucos_Grant_Cap_return_wit_3_prio_invalid.
Axiom proof_of_ucos_Grant_Cap_return_wit_4_class_invalid : ucos_Grant_Cap_return_wit_4_class_invalid.
Axiom proof_of_ucos_Grant_Cap_partial_solve_wit_1_null_target : ucos_Grant_Cap_partial_solve_wit_1_null_target.
Axiom proof_of_ucos_Grant_Cap_partial_solve_wit_2_valid_target : ucos_Grant_Cap_partial_solve_wit_2_valid_target.
Axiom proof_of_ucos_Grant_Cap_partial_solve_wit_3_valid_target : ucos_Grant_Cap_partial_solve_wit_3_valid_target.
Axiom proof_of_ucos_Grant_Cap_partial_solve_wit_4_valid_target : ucos_Grant_Cap_partial_solve_wit_4_valid_target.
Axiom proof_of_ucos_Grant_Cap_partial_solve_wit_5_valid_target : ucos_Grant_Cap_partial_solve_wit_5_valid_target.
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
