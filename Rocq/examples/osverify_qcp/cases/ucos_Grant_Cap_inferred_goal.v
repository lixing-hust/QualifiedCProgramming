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
Require Import SimpleC.EE.osverify_qcp.cases.ucos_Grant_Cap_inferred_lib.
Local Open Scope sac.

(*----- Function ucos_Grant_Cap -----*)

Definition ucos_Grant_Cap_safety_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (0 <= cap_Right_pre)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= 16)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (p <> 0)) (PreH11 : (0 <= old_right)) (PreH12 : (old_right <= UINT_MAX)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (p: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (0 <= cap_Right_pre)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= 16)) (PreH9 : (destTask_Prio_pre < 64)) (PreH10 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (0 <= cap_Right_pre)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (0 <= cap_Right_pre)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (destTask_Prio_pre >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (p: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= 16)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_7 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= 16)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (p <> 0)) (PreH12 : (0 <= old_right)) (PreH13 : (old_right <= UINT_MAX)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= 16)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (p <> 0)) (PreH12 : (0 <= old_right)) (PreH13 : (old_right <= UINT_MAX)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition ucos_Grant_Cap_safety_wit_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (p: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= 16)) (PreH10 : (destTask_Prio_pre < 64)) (PreH11 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition ucos_Grant_Cap_safety_wit_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (destTask_Prio_pre >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition ucos_Grant_Cap_safety_wit_11 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= 16)) (PreH11 : (destTask_Prio_pre < 64)) (PreH12 : (p <> 0)) (PreH13 : (0 <= old_right)) (PreH14 : (old_right <= UINT_MAX)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_12 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (p: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= 16)) (PreH11 : (destTask_Prio_pre < 64)) (PreH12 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_13 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (destTask_Prio_pre >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_14 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (p: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= 16)) (PreH11 : (destTask_Prio_pre < 64)) (PreH12 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_15 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= 16)) (PreH11 : (destTask_Prio_pre < 64)) (PreH12 : (p <> 0)) (PreH13 : (0 <= old_right)) (PreH14 : (old_right <= UINT_MAX)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_16 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (destTask_Prio_pre < 64)) (PreH13 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_17 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (destTask_Prio_pre < 64)) (PreH13 : (p <> 0)) (PreH14 : (0 <= old_right)) (PreH15 : (old_right <= UINT_MAX)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_18 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (destTask_Prio_pre < 64)) (PreH13 : (p <> 0)) (PreH14 : (0 <= old_right)) (PreH15 : (old_right <= UINT_MAX)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> old_right)
|--
  “ (4095 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4095) ”
.

Definition ucos_Grant_Cap_safety_wit_19 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (destTask_Prio_pre < 64)) (PreH13 : (p <> 0)) (PreH14 : (0 <= old_right)) (PreH15 : (old_right <= UINT_MAX)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) cap_Right_pre))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_return_wit_1 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (destTask_Prio_pre < 64)) (PreH13 : (p <> 0)) (PreH14 : (0 <= old_right)) (PreH15 : (old_right <= UINT_MAX)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land old_right 4095) cap_Right_pre))
|--
  EX (new_type: Z)  (new_content: Z)  (new_right: Z) ,
  “ (cap_Class_pre <= 16) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (p <> 0) ” 
  &&  “ (grant_success_fields cap_Class_pre old_right cap_Right_pre 0 new_type new_content new_right ) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> new_type)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> new_content)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> new_right)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (destTask_Prio_pre < 64)) (PreH13 : (p <> 0)) (PreH14 : (0 <= old_right)) (PreH15 : (old_right <= UINT_MAX)) ,
  TT && emp 
|--
  “ (grant_success_fields cap_Class_pre old_right cap_Right_pre 0 1 cap_Class_pre (Z.lor (Z.land old_right 4095) cap_Right_pre) ) ”
  &&  emp
).

Definition ucos_Grant_Cap_return_wit_1_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (old_right: Z) (p: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (destTask_Prio_pre < 64)) (PreH13 : (p <> 0)) (PreH14 : (0 <= old_right)) (PreH15 : (old_right <= UINT_MAX)) ,
  (grant_success_fields cap_Class_pre old_right cap_Right_pre 0 1 cap_Class_pre (Z.lor (Z.land old_right 4095) cap_Right_pre) )
.

Definition ucos_Grant_Cap_return_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (p: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (0 <= cap_Class_pre)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (0 <= cap_Right_pre)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (destTask_Prio_pre < 64)) (PreH13 : (p = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (cap_Class_pre <= 16) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (p = 0) ” 
  &&  “ (11 = 11) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> p)
.

Definition ucos_Grant_Cap_return_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= destTask_Prio_pre)) (PreH5 : (destTask_Prio_pre <= 255)) (PreH6 : (0 <= cap_Class_pre)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (0 <= cap_Right_pre)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (destTask_Prio_pre >= 64)) ,
  TT && emp 
|--
  “ (destTask_Prio_pre >= 64) ” 
  &&  “ (11 = 11) ”
  &&  emp
.

Definition ucos_Grant_Cap_return_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  (“ (cap_Class_pre > 16) ” 
  &&  “ (11 = 11) ”
  &&  emp)
  ||
  (“ (destTask_Prio_pre >= 64) ” 
  &&  “ (11 = 11) ”
  &&  emp)
.

Definition ucos_Grant_Cap_return_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (0 <= cap_Right_pre)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (destTask_Prio_pre >= 64)) ,
  TT && emp 
|--
  (“ (cap_Class_pre > 16) ” 
  &&  “ (11 = 11) ”
  &&  emp)
  ||
  (“ (destTask_Prio_pre >= 64) ” 
  &&  “ (11 = 11) ”
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
Axiom proof_of_ucos_Grant_Cap_safety_wit_15 : ucos_Grant_Cap_safety_wit_15.
Axiom proof_of_ucos_Grant_Cap_safety_wit_16 : ucos_Grant_Cap_safety_wit_16.
Axiom proof_of_ucos_Grant_Cap_safety_wit_17 : ucos_Grant_Cap_safety_wit_17.
Axiom proof_of_ucos_Grant_Cap_safety_wit_18 : ucos_Grant_Cap_safety_wit_18.
Axiom proof_of_ucos_Grant_Cap_safety_wit_19 : ucos_Grant_Cap_safety_wit_19.
Axiom proof_of_ucos_Grant_Cap_return_wit_1 : ucos_Grant_Cap_return_wit_1.
Axiom proof_of_ucos_Grant_Cap_return_wit_2 : ucos_Grant_Cap_return_wit_2.
Axiom proof_of_ucos_Grant_Cap_return_wit_3 : ucos_Grant_Cap_return_wit_3.
Axiom proof_of_ucos_Grant_Cap_return_wit_4 : ucos_Grant_Cap_return_wit_4.
Axiom proof_of_ucos_Grant_Cap_return_wit_5 : ucos_Grant_Cap_return_wit_5.

End VC_Correct.
