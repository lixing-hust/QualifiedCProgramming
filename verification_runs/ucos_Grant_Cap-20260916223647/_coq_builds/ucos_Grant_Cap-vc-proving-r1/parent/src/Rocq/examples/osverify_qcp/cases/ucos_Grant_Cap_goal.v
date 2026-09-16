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
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (target_valid_target <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (destTask_Prio_pre = dest_valid_target)) (PreH6 : (cap_Class_pre = class_valid_target)) (PreH7 : (cap_Right_pre = right_valid_target)) (PreH8 : (0 <= dest_valid_target)) (PreH9 : (dest_valid_target <= 255)) (PreH10 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH11 : (0 <= class_valid_target)) (PreH12 : (class_valid_target <= 16)) (PreH13 : (0 <= right_valid_target)) (PreH14 : (right_valid_target <= UINT_MAX)) (PreH15 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH16 : (target_valid_target <> 0)) ,
  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre))
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
|--
  “ (0 = 0) ” 
  &&  “ (grant_cap_transition 0 class_valid_target right_valid_target old_type_valid_target old_content_valid_target old_right_valid_target 1 class_valid_target (Z.lor (Z.land old_right_valid_target 4095) right_valid_target) ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) right_valid_target))
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (1 <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : ((Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) <= UINT_MAX)) (PreH4 : (1 >= 0)) (PreH5 : (cap_Class_pre >= 0)) (PreH6 : ((Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) >= 0)) (PreH7 : (target_valid_target <> 0)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (cap_Class_pre <= 16)) (PreH10 : (0 <= cap_Class_pre)) (PreH11 : (destTask_Prio_pre = dest_valid_target)) (PreH12 : (cap_Class_pre = class_valid_target)) (PreH13 : (cap_Right_pre = right_valid_target)) (PreH14 : (0 <= dest_valid_target)) (PreH15 : (dest_valid_target <= 255)) (PreH16 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH17 : (0 <= class_valid_target)) (PreH18 : (class_valid_target <= 16)) (PreH19 : (0 <= right_valid_target)) (PreH20 : (right_valid_target <= UINT_MAX)) (PreH21 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH22 : (target_valid_target <> 0)) ,
  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre))
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
|--
  “ (grant_cap_transition 0 cap_Class_pre cap_Right_pre old_type_valid_target old_content_valid_target old_right_valid_target 1 cap_Class_pre (Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (dest_valid_target * sizeof(PTR)))) # Ptr  |-> target_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class_valid_target)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class_valid_target * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) right_valid_target))
).

Definition ucos_Grant_Cap_return_wit_1_valid_target_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right_valid_target: Z) (old_content_valid_target: Z) (old_type_valid_target: Z) (right_valid_target: Z) (class_valid_target: Z) (dest_valid_target: Z) (target_valid_target: Z) (PreH1 : (1 <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : ((Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) <= UINT_MAX)) (PreH4 : (1 >= 0)) (PreH5 : (cap_Class_pre >= 0)) (PreH6 : ((Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) >= 0)) (PreH7 : (target_valid_target <> 0)) (PreH8 : (destTask_Prio_pre < 64)) (PreH9 : (cap_Class_pre <= 16)) (PreH10 : (0 <= cap_Class_pre)) (PreH11 : (destTask_Prio_pre = dest_valid_target)) (PreH12 : (cap_Class_pre = class_valid_target)) (PreH13 : (cap_Right_pre = right_valid_target)) (PreH14 : (0 <= dest_valid_target)) (PreH15 : (dest_valid_target <= 255)) (PreH16 : ((unsigned_last_nbits (dest_valid_target) (32)) = dest_valid_target)) (PreH17 : (0 <= class_valid_target)) (PreH18 : (class_valid_target <= 16)) (PreH19 : (0 <= right_valid_target)) (PreH20 : (right_valid_target <= UINT_MAX)) (PreH21 : ((unsigned_last_nbits (dest_valid_target) (32)) < 64)) (PreH22 : (target_valid_target <> 0)) ,
  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre))
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target_valid_target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target_valid_target)
|--
  “ (grant_cap_transition 0 cap_Class_pre cap_Right_pre old_type_valid_target old_content_valid_target old_right_valid_target 1 cap_Class_pre (Z.lor (Z.land old_right_valid_target 4095) cap_Right_pre) ) ”
.

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

End VC_Correct.
