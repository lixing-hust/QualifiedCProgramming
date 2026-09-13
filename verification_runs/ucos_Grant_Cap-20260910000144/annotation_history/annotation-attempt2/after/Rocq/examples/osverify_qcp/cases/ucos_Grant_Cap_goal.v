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
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Right_pre = right)) (PreH10 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Right_pre = right)) (PreH10 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (target: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Right_pre = right)) (PreH10 : (cap_Class_pre <= 16)) (PreH11 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64)) (PreH12 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (target: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Right_pre = right)) (PreH10 : (cap_Class_pre <= 16)) (PreH11 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64)) (PreH12 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (target: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64)) (PreH13 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (target: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64)) (PreH13 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_7 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre = right)) (PreH12 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (target: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre = right)) (PreH12 : (cap_Class_pre <= 16)) (PreH13 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64)) (PreH14 : (target <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (target: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre = right)) (PreH12 : (cap_Class_pre <= 16)) (PreH13 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64)) (PreH14 : (target = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_11 := 
forall (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : (cap_Class <= 16)) (PreH2 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH3 : (target <> 0)) ,
  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_12 := 
forall (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : (cap_Class <= 16)) (PreH2 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH3 : (target = 0)) ,
  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_13 := 
forall (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : (target = 0)) (PreH2 : (cap_Class <= 16)) (PreH3 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH4 : (target <> 0)) ,
  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_14 := 
forall (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : (target <> 0)) (PreH2 : (cap_Class <= 16)) (PreH3 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH4 : (target = 0)) ,
  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ False ”
.

Definition ucos_Grant_Cap_entail_wit_1_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (old_content: Z) (old_type: Z) (right: Z) (target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre = right)) (PreH12 : (cap_Class_pre <= 16)) (PreH13 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64)) (PreH14 : (target <> 0)) ,
  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (cap_Class_pre <= 16) ” 
  &&  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64) ” 
  &&  “ (target <> 0) ”
  &&  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> old_type)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> old_content)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
.

Definition ucos_Grant_Cap_entail_wit_1_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (target: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre = right)) (PreH12 : (cap_Class_pre <= 16)) (PreH13 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64)) (PreH14 : (target = 0)) ,
  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
|--
  “ (cap_Class_pre <= 16) ” 
  &&  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64) ” 
  &&  “ (target = 0) ”
  &&  ((( &( "cap_Right" ) )) # UInt  |-> right)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
.

Definition ucos_Grant_Cap_return_wit_1 := 
(
forall (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : (target <> 0)) (PreH2 : (cap_Class <= 16)) (PreH3 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH4 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
|--
  “ (0 = 0) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64) ” 
  &&  “ (target <> 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
) \/
(
forall (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : ((Z.lor (Z.land old_right 4095) right) <= UINT_MAX)) (PreH2 : (cap_Class <= UINT_MAX)) (PreH3 : (1 <= UINT_MAX)) (PreH4 : ((Z.lor (Z.land old_right 4095) right) >= 0)) (PreH5 : (cap_Class >= 0)) (PreH6 : (1 >= 0)) (PreH7 : (target <> 0)) (PreH8 : (cap_Class <= 16)) (PreH9 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH10 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
|--
  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64) ” 
  &&  “ (cap_Class_pre <= 16) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
).

Definition ucos_Grant_Cap_return_wit_1_split_goal_1 := 
forall (destTask_Prio_pre: Z) (old_right: Z) (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : ((Z.lor (Z.land old_right 4095) right) <= UINT_MAX)) (PreH2 : (cap_Class <= UINT_MAX)) (PreH3 : (1 <= UINT_MAX)) (PreH4 : ((Z.lor (Z.land old_right 4095) right) >= 0)) (PreH5 : (cap_Class >= 0)) (PreH6 : (1 >= 0)) (PreH7 : (target <> 0)) (PreH8 : (cap_Class <= 16)) (PreH9 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH10 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
|--
  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64) ”
.

Definition ucos_Grant_Cap_return_wit_1_split_goal_2 := 
forall (cap_Class_pre: Z) (old_right: Z) (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : ((Z.lor (Z.land old_right 4095) right) <= UINT_MAX)) (PreH2 : (cap_Class <= UINT_MAX)) (PreH3 : (1 <= UINT_MAX)) (PreH4 : ((Z.lor (Z.land old_right 4095) right) >= 0)) (PreH5 : (cap_Class >= 0)) (PreH6 : (1 >= 0)) (PreH7 : (target <> 0)) (PreH8 : (cap_Class <= 16)) (PreH9 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH10 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
|--
  “ (cap_Class_pre <= 16) ”
.

Definition ucos_Grant_Cap_return_wit_1_split_goal_spatial := 
forall (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (right: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : ((Z.lor (Z.land old_right 4095) right) <= UINT_MAX)) (PreH2 : (cap_Class <= UINT_MAX)) (PreH3 : (1 <= UINT_MAX)) (PreH4 : ((Z.lor (Z.land old_right 4095) right) >= 0)) (PreH5 : (cap_Class >= 0)) (PreH6 : (1 >= 0)) (PreH7 : (target <> 0)) (PreH8 : (cap_Class <= 16)) (PreH9 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH10 : (target <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
|--
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> target)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((target)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) right))
.

Definition ucos_Grant_Cap_return_wit_2 := 
forall (cap_Class_pre: Z) (destTask_Prio_pre: Z) (target: Z) (cap_Class: Z) (destTask_Prio: Z) (PreH1 : (target = 0)) (PreH2 : (cap_Class <= 16)) (PreH3 : ((unsigned_last_nbits (destTask_Prio) (32)) < 64)) (PreH4 : (target = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio * sizeof(PTR)))) # Ptr  |-> target)
|--
  (“ (11 = 11) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) < 64) ” 
  &&  “ (target = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> 0))
  ||
  (“ (11 = 11) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  emp)
  ||
  (“ (11 = 11) ” 
  &&  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) >= 64) ”
  &&  emp)
.

Definition ucos_Grant_Cap_return_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre = right)) (PreH12 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) >= 64)) ,
  TT && emp 
|--
  “ (11 = 11) ” 
  &&  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) >= 64) ”
  &&  emp
.

Definition ucos_Grant_Cap_return_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Right_pre = right)) (PreH11 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  (“ (11 = 11) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  emp)
  ||
  (“ (11 = 11) ” 
  &&  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) >= 64) ”
  &&  emp)
.

Definition ucos_Grant_Cap_return_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) = destTask_Prio_pre)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Right_pre = right)) (PreH11 : ((unsigned_last_nbits (destTask_Prio_pre) (32)) >= 64)) ,
  TT && emp 
|--
  (“ (11 = 11) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  emp)
  ||
  (“ (11 = 11) ” 
  &&  “ ((unsigned_last_nbits (destTask_Prio_pre) (32)) >= 64) ”
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
