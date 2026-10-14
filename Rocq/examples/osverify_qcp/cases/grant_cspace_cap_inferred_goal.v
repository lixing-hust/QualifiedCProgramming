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
Require Import SimpleC.EE.osverify_qcp.cases.grant_cspace_cap_inferred_lib.
Local Open Scope sac.

(*----- Function ucos_Grant_Cap -----*)

Definition ucos_Grant_Cap_safety_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (dp: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (destTask_Prio_pre < 64)) (PreH5 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (destTask_Prio_pre >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (0 > cap_Class_pre)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (cap_Class_pre <= 16)) (PreH5 : (destTask_Prio_pre >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_7 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (dp: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (cap_Class_pre <= 16)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (cap_Class_pre <= 16)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (cap_Class_pre <= 16)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition ucos_Grant_Cap_safety_wit_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (dp: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (cap_Class_pre <= 16)) (PreH5 : (destTask_Prio_pre < 64)) (PreH6 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition ucos_Grant_Cap_safety_wit_11 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (cap_Class_pre <= 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (cap_Class_pre <= 16)) (PreH5 : (destTask_Prio_pre >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition ucos_Grant_Cap_safety_wit_12 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= 16)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_13 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (dp: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= 16)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_14 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= 16)) (PreH6 : (destTask_Prio_pre >= 64)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_15 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (dp: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= 16)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_16 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (destTask_Prio_pre < 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= 16)) (PreH6 : (destTask_Prio_pre < 64)) (PreH7 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_safety_wit_17 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (dp: Z) (PreH1 : (dp <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= 16)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_18 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (dp = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= 16)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition ucos_Grant_Cap_safety_wit_19 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (dp <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= 16)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (4095 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4095) ”
.

Definition ucos_Grant_Cap_safety_wit_20 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (dp <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= 16)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land oldright 4095) cap_Right_pre))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ucos_Grant_Cap_entail_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (grant_call_pre destTask_Prio_pre cap_Class_pre dp oldright )
|--
  “ (0 <= cap_Class_pre) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ”
  &&  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  (grant_call_pre destTask_Prio_pre cap_Class_pre dp oldright )
.

Definition ucos_Grant_Cap_entail_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (0 <= cap_Class_pre)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) ,
  (grant_call_pre destTask_Prio_pre cap_Class_pre dp oldright )
|--
  (“ (0 <= cap_Class_pre) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (dp <> 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright))
  ||
  (“ (0 <= cap_Class_pre) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (dp = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp))
  ||
  (“ (0 <= cap_Class_pre) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (destTask_Prio_pre >= 64) ”
  &&  emp)
  ||
  (“ (0 <= cap_Class_pre) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  emp)
.

Definition ucos_Grant_Cap_return_wit_1 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (dp <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= 16)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (Z.lor (Z.land oldright 4095) cap_Right_pre))
|--
  “ (cap_Class_pre <= 16) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (0 = 0) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> cap_Class_pre)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (cap_Right_pre)))
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (dp <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= 16)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (dp <> 0)) ,
  TT && emp 
|--
  “ ((Z.lor (Z.land oldright 4095) cap_Right_pre) = (grant_rights (oldright) (cap_Right_pre))) ”
  &&  emp
).

Definition ucos_Grant_Cap_return_wit_1_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (oldright: Z) (dp: Z) (PreH1 : (dp <> 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= 16)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (dp <> 0)) ,
  ((Z.lor (Z.land oldright 4095) cap_Right_pre) = (grant_rights (oldright) (cap_Right_pre)))
.

Definition ucos_Grant_Cap_return_wit_2 := 
forall (cap_Class_pre: Z) (destTask_Prio_pre: Z) (dp: Z) (PreH1 : (dp = 0)) (PreH2 : (destTask_Prio_pre < 64)) (PreH3 : (cap_Class_pre <= 16)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (0 <= cap_Class_pre)) (PreH6 : (cap_Class_pre <= 16)) (PreH7 : (destTask_Prio_pre < 64)) (PreH8 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ (cap_Class_pre <= 16) ” 
  &&  “ (destTask_Prio_pre < 64) ” 
  &&  “ (dp = 0) ” 
  &&  “ (11 = 11) ”
  &&  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
.

Definition ucos_Grant_Cap_return_wit_3 := 
forall (cap_Class_pre: Z) (destTask_Prio_pre: Z) (PreH1 : (destTask_Prio_pre >= 64)) (PreH2 : (cap_Class_pre <= 16)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (0 <= cap_Class_pre)) (PreH5 : (cap_Class_pre <= 16)) (PreH6 : (destTask_Prio_pre >= 64)) ,
  TT && emp 
|--
  “ (cap_Class_pre <= 16) ” 
  &&  “ (destTask_Prio_pre >= 64) ” 
  &&  “ (11 = 11) ”
  &&  emp
.

Definition ucos_Grant_Cap_return_wit_4 := 
forall (cap_Class_pre: Z) (PreH1 : (cap_Class_pre > 16)) (PreH2 : (0 <= cap_Class_pre)) (PreH3 : (0 <= cap_Class_pre)) (PreH4 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  “ (cap_Class_pre > 16) ” 
  &&  “ (11 = 11) ”
  &&  emp
.

(*----- Function grant_cspace_cap -----*)

Definition grant_cspace_cap_safety_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (auth >= 0)) (PreH10 : (cap_Right_pre >= 0)) (PreH11 : (cap_Class_pre >= 0)) (PreH12 : (destTask_Prio_pre = dest0)) (PreH13 : (cap_Class_pre = class0)) (PreH14 : (cap_Right_pre = right0)) (PreH15 : (destTask_Prio_pre < 63)) (PreH16 : (0 <= q)) (PreH17 : (q < 64)) (PreH18 : (cp <> 0)) (PreH19 : (p <> 0)) (PreH20 : (run <> 0)) (PreH21 : ((Z.land auth 64) <> 0)) (PreH22 : (parent = q)) (PreH23 : (destTask_Prio_pre <> q)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (auth >= 0)) (PreH10 : (cap_Right_pre >= 0)) (PreH11 : (cap_Class_pre >= 0)) (PreH12 : (destTask_Prio_pre = dest0)) (PreH13 : (cap_Class_pre = class0)) (PreH14 : (cap_Right_pre = right0)) (PreH15 : (destTask_Prio_pre < 63)) (PreH16 : (0 <= q)) (PreH17 : (q < 64)) (PreH18 : (cp <> 0)) (PreH19 : (p <> 0)) (PreH20 : (run <> 0)) (PreH21 : ((Z.land auth 64) <> 0)) (PreH22 : (parent = q)) (PreH23 : (destTask_Prio_pre <> q)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent = q)) (PreH21 : (destTask_Prio_pre <> q)) (PreH22 : (cap_Class_pre <= 16)) (PreH23 : (dp <> 0)) (PreH24 : (p = dp)) (PreH25 : (cap_Class_pre = 11)) (PreH26 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent = q)) (PreH21 : (destTask_Prio_pre <> q)) (PreH22 : (cap_Class_pre <= 16)) (PreH23 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (auth >= 0)) (PreH10 : (cap_Right_pre >= 0)) (PreH11 : (cap_Class_pre >= 0)) (PreH12 : (destTask_Prio_pre = dest0)) (PreH13 : (cap_Class_pre = class0)) (PreH14 : (cap_Right_pre = right0)) (PreH15 : (destTask_Prio_pre < 63)) (PreH16 : (0 <= q)) (PreH17 : (q < 64)) (PreH18 : (cp <> 0)) (PreH19 : (p <> 0)) (PreH20 : (run <> 0)) (PreH21 : ((Z.land auth 64) <> 0)) (PreH22 : (parent = q)) (PreH23 : (destTask_Prio_pre = q)) (PreH24 : (dp = p)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent = q)) (PreH21 : (destTask_Prio_pre = q)) (PreH22 : (dp = p)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (cap_Class_pre = 11)) (PreH27 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_7 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent = q)) (PreH21 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run = 0)) (PreH19 : (destTask_Prio_pre <> q)) (PreH20 : (cap_Class_pre <= 16)) (PreH21 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (cap_Right_pre >= 0)) (PreH7 : (cap_Class_pre >= 0)) (PreH8 : (destTask_Prio_pre = dest0)) (PreH9 : (cap_Class_pre = class0)) (PreH10 : (cap_Right_pre = right0)) (PreH11 : (destTask_Prio_pre < 63)) (PreH12 : (0 <= q)) (PreH13 : (q < 64)) (PreH14 : (cp <> 0)) (PreH15 : (p <> 0)) (PreH16 : (run = 0)) (PreH17 : (destTask_Prio_pre <> q)) (PreH18 : (cap_Class_pre <= 16)) (PreH19 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run = 0)) (PreH19 : (destTask_Prio_pre = q)) (PreH20 : (dp = p)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_11 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (cap_Right_pre >= 0)) (PreH7 : (cap_Class_pre >= 0)) (PreH8 : (destTask_Prio_pre = dest0)) (PreH9 : (cap_Class_pre = class0)) (PreH10 : (cap_Right_pre = right0)) (PreH11 : (destTask_Prio_pre < 63)) (PreH12 : (0 <= q)) (PreH13 : (q < 64)) (PreH14 : (cp <> 0)) (PreH15 : (p <> 0)) (PreH16 : (run = 0)) (PreH17 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_12 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_13 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_14 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (cap_Right_pre >= 0)) (PreH7 : (cap_Class_pre >= 0)) (PreH8 : (destTask_Prio_pre = dest0)) (PreH9 : (cap_Class_pre = class0)) (PreH10 : (cap_Right_pre = right0)) (PreH11 : (destTask_Prio_pre < 63)) (PreH12 : (0 <= q)) (PreH13 : (q < 64)) (PreH14 : (cp <> 0)) (PreH15 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_15 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (cap_Right_pre >= 0)) (PreH7 : (cap_Class_pre >= 0)) (PreH8 : (destTask_Prio_pre = dest0)) (PreH9 : (cap_Class_pre = class0)) (PreH10 : (cap_Right_pre = right0)) (PreH11 : (destTask_Prio_pre >= 63)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_16 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (auth >= 0)) (PreH10 : (cap_Right_pre >= 0)) (PreH11 : (cap_Class_pre >= 0)) (PreH12 : (destTask_Prio_pre = dest0)) (PreH13 : (cap_Class_pre = class0)) (PreH14 : (cap_Right_pre = right0)) (PreH15 : (destTask_Prio_pre < 63)) (PreH16 : (0 <= q)) (PreH17 : (q < 64)) (PreH18 : (cp <> 0)) (PreH19 : (p <> 0)) (PreH20 : (run <> 0)) (PreH21 : ((Z.land auth 64) <> 0)) (PreH22 : (parent = q)) (PreH23 : (destTask_Prio_pre <> q)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_17 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (auth >= 0)) (PreH10 : (cap_Right_pre >= 0)) (PreH11 : (cap_Class_pre >= 0)) (PreH12 : (destTask_Prio_pre = dest0)) (PreH13 : (cap_Class_pre = class0)) (PreH14 : (cap_Right_pre = right0)) (PreH15 : (destTask_Prio_pre < 63)) (PreH16 : (0 <= q)) (PreH17 : (q < 64)) (PreH18 : (cp <> 0)) (PreH19 : (p <> 0)) (PreH20 : (run <> 0)) (PreH21 : ((Z.land auth 64) <> 0)) (PreH22 : (parent = q)) (PreH23 : (destTask_Prio_pre <> q)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_18 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent = q)) (PreH21 : (destTask_Prio_pre <> q)) (PreH22 : (cap_Class_pre <= 16)) (PreH23 : (dp <> 0)) (PreH24 : (p = dp)) (PreH25 : (cap_Class_pre = 11)) (PreH26 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_19 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent = q)) (PreH21 : (destTask_Prio_pre <> q)) (PreH22 : (cap_Class_pre <= 16)) (PreH23 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_20 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (auth >= 0)) (PreH10 : (cap_Right_pre >= 0)) (PreH11 : (cap_Class_pre >= 0)) (PreH12 : (destTask_Prio_pre = dest0)) (PreH13 : (cap_Class_pre = class0)) (PreH14 : (cap_Right_pre = right0)) (PreH15 : (destTask_Prio_pre < 63)) (PreH16 : (0 <= q)) (PreH17 : (q < 64)) (PreH18 : (cp <> 0)) (PreH19 : (p <> 0)) (PreH20 : (run <> 0)) (PreH21 : ((Z.land auth 64) <> 0)) (PreH22 : (parent = q)) (PreH23 : (destTask_Prio_pre = q)) (PreH24 : (dp = p)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_21 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent = q)) (PreH21 : (destTask_Prio_pre = q)) (PreH22 : (dp = p)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (cap_Class_pre = 11)) (PreH27 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_22 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent = q)) (PreH21 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_23 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run = 0)) (PreH19 : (destTask_Prio_pre <> q)) (PreH20 : (cap_Class_pre <= 16)) (PreH21 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_24 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (cap_Right_pre >= 0)) (PreH7 : (cap_Class_pre >= 0)) (PreH8 : (destTask_Prio_pre = dest0)) (PreH9 : (cap_Class_pre = class0)) (PreH10 : (cap_Right_pre = right0)) (PreH11 : (destTask_Prio_pre < 63)) (PreH12 : (0 <= q)) (PreH13 : (q < 64)) (PreH14 : (cp <> 0)) (PreH15 : (p <> 0)) (PreH16 : (run = 0)) (PreH17 : (destTask_Prio_pre <> q)) (PreH18 : (cap_Class_pre <= 16)) (PreH19 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_25 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (oldright <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run = 0)) (PreH19 : (destTask_Prio_pre = q)) (PreH20 : (dp = p)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_26 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (cap_Right_pre >= 0)) (PreH7 : (cap_Class_pre >= 0)) (PreH8 : (destTask_Prio_pre = dest0)) (PreH9 : (cap_Class_pre = class0)) (PreH10 : (cap_Right_pre = right0)) (PreH11 : (destTask_Prio_pre < 63)) (PreH12 : (0 <= q)) (PreH13 : (q < 64)) (PreH14 : (cp <> 0)) (PreH15 : (p <> 0)) (PreH16 : (run = 0)) (PreH17 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_27 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) <> 0)) (PreH20 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_28 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (cap_Right_pre >= 0)) (PreH9 : (cap_Class_pre >= 0)) (PreH10 : (destTask_Prio_pre = dest0)) (PreH11 : (cap_Class_pre = class0)) (PreH12 : (cap_Right_pre = right0)) (PreH13 : (destTask_Prio_pre < 63)) (PreH14 : (0 <= q)) (PreH15 : (q < 64)) (PreH16 : (cp <> 0)) (PreH17 : (p <> 0)) (PreH18 : (run <> 0)) (PreH19 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_29 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre < 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (cap_Right_pre >= 0)) (PreH7 : (cap_Class_pre >= 0)) (PreH8 : (destTask_Prio_pre = dest0)) (PreH9 : (cap_Class_pre = class0)) (PreH10 : (cap_Right_pre = right0)) (PreH11 : (destTask_Prio_pre < 63)) (PreH12 : (0 <= q)) (PreH13 : (q < 64)) (PreH14 : (cp <> 0)) (PreH15 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_30 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_31 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_32 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (cap_Class_pre = 11)) (PreH27 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_33 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_34 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_35 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre = q)) (PreH23 : (dp = p)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (cap_Class_pre = 11)) (PreH28 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_36 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_37 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_38 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run = 0)) (PreH18 : (destTask_Prio_pre <> q)) (PreH19 : (cap_Class_pre <= 16)) (PreH20 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_39 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (destTask_Prio_pre = q)) (PreH21 : (dp = p)) (PreH22 : (cap_Class_pre <= 16)) (PreH23 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_40 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run = 0)) (PreH18 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_41 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_42 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_43 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_44 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (oldright >= 0)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp <> 0)) (PreH31 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_45 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (oldright >= 0)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp <> 0)) (PreH31 : (p = dp)) (PreH32 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_46 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p = dp)) (PreH30 : (cap_Class_pre = 11)) (PreH31 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_47 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (auth <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_48 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (oldright >= 0)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre = q)) (PreH29 : (dp = p)) (PreH30 : (cap_Class_pre <= 16)) (PreH31 : (dp <> 0)) (PreH32 : (p = dp)) (PreH33 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_49 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre = q)) (PreH27 : (dp = p)) (PreH28 : (cap_Class_pre <= 16)) (PreH29 : (dp <> 0)) (PreH30 : (p = dp)) (PreH31 : (cap_Class_pre = 11)) (PreH32 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_50 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (auth <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_51 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run = 0)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_52 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_53 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run = 0)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_54 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_55 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (auth <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_56 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (auth <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_57 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (oldright >= 0)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp <> 0)) (PreH31 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_58 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (oldright >= 0)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp <> 0)) (PreH31 : (p = dp)) (PreH32 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_59 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (auth <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_60 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (oldright >= 0)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre = q)) (PreH29 : (dp = p)) (PreH30 : (cap_Class_pre <= 16)) (PreH31 : (dp <> 0)) (PreH32 : (p = dp)) (PreH33 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_61 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (auth <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_62 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (auth <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_63 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (auth <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_64 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre = q)) (PreH27 : (dp = p)) (PreH28 : (cap_Class_pre <= 16)) (PreH29 : (dp <> 0)) (PreH30 : (p = dp)) (PreH31 : (cap_Class_pre = 11)) (PreH32 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_65 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p = dp)) (PreH30 : (cap_Class_pre = 11)) (PreH31 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition grant_cspace_cap_safety_wit_66 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (oldright <= UINT_MAX)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (oldright >= 0)) (PreH15 : (auth >= 0)) (PreH16 : (cap_Right_pre >= 0)) (PreH17 : (cap_Class_pre >= 0)) (PreH18 : (destTask_Prio_pre = dest0)) (PreH19 : (cap_Class_pre = class0)) (PreH20 : (cap_Right_pre = right0)) (PreH21 : (destTask_Prio_pre < 63)) (PreH22 : (0 <= q)) (PreH23 : (q < 64)) (PreH24 : (cp <> 0)) (PreH25 : (p <> 0)) (PreH26 : (run <> 0)) (PreH27 : ((Z.land auth 64) <> 0)) (PreH28 : (parent = q)) (PreH29 : (destTask_Prio_pre <> q)) (PreH30 : (cap_Class_pre <= 16)) (PreH31 : (dp <> 0)) (PreH32 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_67 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (oldright <= UINT_MAX)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (oldright >= 0)) (PreH15 : (auth >= 0)) (PreH16 : (cap_Right_pre >= 0)) (PreH17 : (cap_Class_pre >= 0)) (PreH18 : (destTask_Prio_pre = dest0)) (PreH19 : (cap_Class_pre = class0)) (PreH20 : (cap_Right_pre = right0)) (PreH21 : (destTask_Prio_pre < 63)) (PreH22 : (0 <= q)) (PreH23 : (q < 64)) (PreH24 : (cp <> 0)) (PreH25 : (p <> 0)) (PreH26 : (run <> 0)) (PreH27 : ((Z.land auth 64) <> 0)) (PreH28 : (parent = q)) (PreH29 : (destTask_Prio_pre <> q)) (PreH30 : (cap_Class_pre <= 16)) (PreH31 : (dp <> 0)) (PreH32 : (p = dp)) (PreH33 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_68 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (auth >= 0)) (PreH14 : (cap_Right_pre >= 0)) (PreH15 : (cap_Class_pre >= 0)) (PreH16 : (destTask_Prio_pre = dest0)) (PreH17 : (cap_Class_pre = class0)) (PreH18 : (cap_Right_pre = right0)) (PreH19 : (destTask_Prio_pre < 63)) (PreH20 : (0 <= q)) (PreH21 : (q < 64)) (PreH22 : (cp <> 0)) (PreH23 : (p <> 0)) (PreH24 : (run <> 0)) (PreH25 : ((Z.land auth 64) <> 0)) (PreH26 : (parent = q)) (PreH27 : (destTask_Prio_pre <> q)) (PreH28 : (cap_Class_pre <= 16)) (PreH29 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_69 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (oldright <= UINT_MAX)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (oldright >= 0)) (PreH15 : (auth >= 0)) (PreH16 : (cap_Right_pre >= 0)) (PreH17 : (cap_Class_pre >= 0)) (PreH18 : (destTask_Prio_pre = dest0)) (PreH19 : (cap_Class_pre = class0)) (PreH20 : (cap_Right_pre = right0)) (PreH21 : (destTask_Prio_pre < 63)) (PreH22 : (0 <= q)) (PreH23 : (q < 64)) (PreH24 : (cp <> 0)) (PreH25 : (p <> 0)) (PreH26 : (run <> 0)) (PreH27 : ((Z.land auth 64) <> 0)) (PreH28 : (parent = q)) (PreH29 : (destTask_Prio_pre = q)) (PreH30 : (dp = p)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p = dp)) (PreH34 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_70 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (auth >= 0)) (PreH14 : (cap_Right_pre >= 0)) (PreH15 : (cap_Class_pre >= 0)) (PreH16 : (destTask_Prio_pre = dest0)) (PreH17 : (cap_Class_pre = class0)) (PreH18 : (cap_Right_pre = right0)) (PreH19 : (destTask_Prio_pre < 63)) (PreH20 : (0 <= q)) (PreH21 : (q < 64)) (PreH22 : (cp <> 0)) (PreH23 : (p <> 0)) (PreH24 : (run <> 0)) (PreH25 : ((Z.land auth 64) <> 0)) (PreH26 : (parent = q)) (PreH27 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_71 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (auth >= 0)) (PreH14 : (cap_Right_pre >= 0)) (PreH15 : (cap_Class_pre >= 0)) (PreH16 : (destTask_Prio_pre = dest0)) (PreH17 : (cap_Class_pre = class0)) (PreH18 : (cap_Right_pre = right0)) (PreH19 : (destTask_Prio_pre < 63)) (PreH20 : (0 <= q)) (PreH21 : (q < 64)) (PreH22 : (cp <> 0)) (PreH23 : (p <> 0)) (PreH24 : (run <> 0)) (PreH25 : ((Z.land auth 64) <> 0)) (PreH26 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_72 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) <> 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (auth >= 0)) (PreH14 : (cap_Right_pre >= 0)) (PreH15 : (cap_Class_pre >= 0)) (PreH16 : (destTask_Prio_pre = dest0)) (PreH17 : (cap_Class_pre = class0)) (PreH18 : (cap_Right_pre = right0)) (PreH19 : (destTask_Prio_pre < 63)) (PreH20 : (0 <= q)) (PreH21 : (q < 64)) (PreH22 : (cp <> 0)) (PreH23 : (p <> 0)) (PreH24 : (run <> 0)) (PreH25 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_73 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (oldright <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (oldright >= 0)) (PreH14 : (cap_Right_pre >= 0)) (PreH15 : (cap_Class_pre >= 0)) (PreH16 : (destTask_Prio_pre = dest0)) (PreH17 : (cap_Class_pre = class0)) (PreH18 : (cap_Right_pre = right0)) (PreH19 : (destTask_Prio_pre < 63)) (PreH20 : (0 <= q)) (PreH21 : (q < 64)) (PreH22 : (cp <> 0)) (PreH23 : (p <> 0)) (PreH24 : (run <> 0)) (PreH25 : ((Z.land auth 64) <> 0)) (PreH26 : (parent = q)) (PreH27 : (destTask_Prio_pre = q)) (PreH28 : (dp = p)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp <> 0)) (PreH31 : (p = dp)) (PreH32 : (cap_Class_pre = 11)) (PreH33 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_74 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (oldright <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (oldright >= 0)) (PreH14 : (cap_Right_pre >= 0)) (PreH15 : (cap_Class_pre >= 0)) (PreH16 : (destTask_Prio_pre = dest0)) (PreH17 : (cap_Class_pre = class0)) (PreH18 : (cap_Right_pre = right0)) (PreH19 : (destTask_Prio_pre < 63)) (PreH20 : (0 <= q)) (PreH21 : (q < 64)) (PreH22 : (cp <> 0)) (PreH23 : (p <> 0)) (PreH24 : (run <> 0)) (PreH25 : ((Z.land auth 64) <> 0)) (PreH26 : (parent = q)) (PreH27 : (destTask_Prio_pre <> q)) (PreH28 : (cap_Class_pre <= 16)) (PreH29 : (dp <> 0)) (PreH30 : (p = dp)) (PreH31 : (cap_Class_pre = 11)) (PreH32 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_75 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent <> q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_76 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent <> q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p = dp)) (PreH34 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_77 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent <> q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_78 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent <> q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre = q)) (PreH31 : (dp = p)) (PreH32 : (cap_Class_pre <= 16)) (PreH33 : (dp <> 0)) (PreH34 : (p = dp)) (PreH35 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_79 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (parent <> q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_80 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_81 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent <> q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (oldright >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre = q)) (PreH29 : (dp = p)) (PreH30 : (cap_Class_pre <= 16)) (PreH31 : (dp <> 0)) (PreH32 : (p = dp)) (PreH33 : (cap_Class_pre = 11)) (PreH34 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_82 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent <> q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (oldright >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp <> 0)) (PreH31 : (p = dp)) (PreH32 : (cap_Class_pre = 11)) (PreH33 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_83 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run = 0)) (PreH10 : (class0 > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_84 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run = 0)) (PreH11 : (class0 > 16)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_85 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp <> 0)) (PreH4 : (retval = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run = 0)) (PreH11 : (class0 > 16)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_86 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run = 0)) (PreH9 : (dest0 = q)) (PreH10 : (dp = p)) (PreH11 : (class0 <= 16)) (PreH12 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_87 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run = 0)) (PreH10 : (dest0 = q)) (PreH11 : (dp = p)) (PreH12 : (class0 <= 16)) (PreH13 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_88 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (p = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run = 0)) (PreH11 : (dest0 = q)) (PreH12 : (dp = p)) (PreH13 : (class0 <= 16)) (PreH14 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_89 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run = 0)) (PreH9 : (dest0 <> q)) (PreH10 : (class0 <= 16)) (PreH11 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_90 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run = 0)) (PreH10 : (dest0 <> q)) (PreH11 : (class0 <= 16)) (PreH12 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_91 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (0 <> 0)) (PreH4 : (retval = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run = 0)) (PreH11 : (dest0 <> q)) (PreH12 : (class0 <= 16)) (PreH13 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((&(((&((0)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((0)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((0)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_92 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run = 0)) (PreH9 : (dest0 <> q)) (PreH10 : (class0 <= 16)) (PreH11 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_93 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run = 0)) (PreH10 : (dest0 <> q)) (PreH11 : (class0 <= 16)) (PreH12 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_94 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run = 0)) (PreH11 : (dest0 <> q)) (PreH12 : (class0 <= 16)) (PreH13 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_95 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (class0 > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_96 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (class0 > 16)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_97 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp <> 0)) (PreH4 : (retval = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (class0 > 16)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_98 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run <> 0)) (PreH9 : ((Z.land auth 64) <> 0)) (PreH10 : (parent = q)) (PreH11 : (dest0 = q)) (PreH12 : (dp = p)) (PreH13 : (class0 <= 16)) (PreH14 : (dp <> 0)) (PreH15 : (p = dp)) (PreH16 : (class0 = 11)) (PreH17 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_99 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (dest0 = q)) (PreH13 : (dp = p)) (PreH14 : (class0 <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p = dp)) (PreH17 : (class0 = 11)) (PreH18 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_100 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 = q)) (PreH14 : (dp = p)) (PreH15 : (class0 <= 16)) (PreH16 : (dp <> 0)) (PreH17 : (p = dp)) (PreH18 : (class0 = 11)) (PreH19 : (oldright = auth)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_101 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run <> 0)) (PreH9 : ((Z.land auth 64) <> 0)) (PreH10 : (parent = q)) (PreH11 : (dest0 = q)) (PreH12 : (dp = p)) (PreH13 : (class0 <= 16)) (PreH14 : (dp <> 0)) (PreH15 : (p = dp)) (PreH16 : (class0 <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_102 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (dest0 = q)) (PreH13 : (dp = p)) (PreH14 : (class0 <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p = dp)) (PreH17 : (class0 <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_103 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 = q)) (PreH14 : (dp = p)) (PreH15 : (class0 <= 16)) (PreH16 : (dp <> 0)) (PreH17 : (p = dp)) (PreH18 : (class0 <> 11)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_104 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run <> 0)) (PreH9 : ((Z.land auth 64) <> 0)) (PreH10 : (parent = q)) (PreH11 : (dest0 <> q)) (PreH12 : (class0 <= 16)) (PreH13 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_105 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (dest0 <> q)) (PreH13 : (class0 <= 16)) (PreH14 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_106 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (0 <> 0)) (PreH4 : (retval = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 <> q)) (PreH14 : (class0 <= 16)) (PreH15 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((&(((&((0)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((0)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((0)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_107 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run <> 0)) (PreH9 : ((Z.land auth 64) <> 0)) (PreH10 : (parent = q)) (PreH11 : (dest0 <> q)) (PreH12 : (class0 <= 16)) (PreH13 : (dp <> 0)) (PreH14 : (p = dp)) (PreH15 : (class0 = 11)) (PreH16 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_108 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (dest0 <> q)) (PreH13 : (class0 <= 16)) (PreH14 : (dp <> 0)) (PreH15 : (p = dp)) (PreH16 : (class0 = 11)) (PreH17 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_109 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 <> q)) (PreH14 : (class0 <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p = dp)) (PreH17 : (class0 = 11)) (PreH18 : (oldright = auth)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_110 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run <> 0)) (PreH9 : ((Z.land auth 64) <> 0)) (PreH10 : (parent = q)) (PreH11 : (dest0 <> q)) (PreH12 : (class0 <= 16)) (PreH13 : (dp <> 0)) (PreH14 : (p = dp)) (PreH15 : (class0 <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_111 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (dest0 <> q)) (PreH13 : (class0 <= 16)) (PreH14 : (dp <> 0)) (PreH15 : (p = dp)) (PreH16 : (class0 <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_112 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 <> q)) (PreH14 : (class0 <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p = dp)) (PreH17 : (class0 <> 11)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_113 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run <> 0)) (PreH9 : ((Z.land auth 64) <> 0)) (PreH10 : (parent = q)) (PreH11 : (dest0 <> q)) (PreH12 : (class0 <= 16)) (PreH13 : (dp <> 0)) (PreH14 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_114 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 >= 64)) (PreH3 : (retval = 11)) (PreH4 : (dest0 < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (dest0 <> q)) (PreH13 : (class0 <= 16)) (PreH14 : (dp <> 0)) (PreH15 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_115 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp = 0)) (PreH4 : (retval = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 <> q)) (PreH14 : (class0 <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p <> dp)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |->_)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_116 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : (class0 <= UINT_MAX)) (PreH4 : (right0 >= 0)) (PreH5 : (class0 >= 0)) (PreH6 : (class0 > 16)) (PreH7 : (retval = 11)) (PreH8 : (dest0 < 63)) (PreH9 : (0 <= q)) (PreH10 : (q < 64)) (PreH11 : (cp <> 0)) (PreH12 : (p <> 0)) (PreH13 : (run = 0)) (PreH14 : (class0 > 16)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_117 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (1 <= UINT_MAX)) (PreH6 : (right0 >= 0)) (PreH7 : ((grant_rights (oldright) (right0)) >= 0)) (PreH8 : (class0 >= 0)) (PreH9 : (1 >= 0)) (PreH10 : (class0 <= 16)) (PreH11 : (dest0 < 64)) (PreH12 : (p <> 0)) (PreH13 : (retval = 0)) (PreH14 : (dest0 < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (dest0 = q)) (PreH21 : (dp = p)) (PreH22 : (class0 <= 16)) (PreH23 : (dp <> 0)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_118 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : (class0 <= UINT_MAX)) (PreH4 : (right0 >= 0)) (PreH5 : (class0 >= 0)) (PreH6 : (class0 <= 16)) (PreH7 : (dest0 < 64)) (PreH8 : (retval = 11)) (PreH9 : (dest0 < 63)) (PreH10 : (0 <= q)) (PreH11 : (q < 64)) (PreH12 : (cp <> 0)) (PreH13 : (p <> 0)) (PreH14 : (run = 0)) (PreH15 : (dest0 <> q)) (PreH16 : (class0 <= 16)) (PreH17 : (dp = 0)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_119 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (1 <= UINT_MAX)) (PreH6 : (right0 >= 0)) (PreH7 : ((grant_rights (oldright) (right0)) >= 0)) (PreH8 : (class0 >= 0)) (PreH9 : (1 >= 0)) (PreH10 : (class0 <= 16)) (PreH11 : (dest0 < 64)) (PreH12 : (dp <> 0)) (PreH13 : (retval = 0)) (PreH14 : (dest0 < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (dest0 <> q)) (PreH21 : (class0 <= 16)) (PreH22 : (dp <> 0)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_120 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (auth >= 0)) (PreH6 : (right0 >= 0)) (PreH7 : (class0 >= 0)) (PreH8 : (class0 > 16)) (PreH9 : (retval = 11)) (PreH10 : (dest0 < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent = q)) (PreH18 : (class0 > 16)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_121 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : ((grant_rights (auth) (right0)) <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (1 <= UINT_MAX)) (PreH6 : (right0 >= 0)) (PreH7 : ((grant_rights (auth) (right0)) >= 0)) (PreH8 : (class0 >= 0)) (PreH9 : (1 >= 0)) (PreH10 : (class0 <= 16)) (PreH11 : (dest0 < 64)) (PreH12 : (dp <> 0)) (PreH13 : (retval = 0)) (PreH14 : (dest0 < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (dest0 = q)) (PreH23 : (dp = p)) (PreH24 : (class0 <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (class0 = 11)) (PreH28 : (oldright = auth)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (auth) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_122 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH5 : (class0 <= UINT_MAX)) (PreH6 : (1 <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (right0 >= 0)) (PreH9 : ((grant_rights (oldright) (right0)) >= 0)) (PreH10 : (class0 >= 0)) (PreH11 : (1 >= 0)) (PreH12 : (class0 <= 16)) (PreH13 : (dest0 < 64)) (PreH14 : (dp <> 0)) (PreH15 : (retval = 0)) (PreH16 : (dest0 < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (dest0 = q)) (PreH25 : (dp = p)) (PreH26 : (class0 <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (class0 <> 11)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_123 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (auth >= 0)) (PreH6 : (right0 >= 0)) (PreH7 : (class0 >= 0)) (PreH8 : (class0 <= 16)) (PreH9 : (dest0 < 64)) (PreH10 : (retval = 11)) (PreH11 : (dest0 < 63)) (PreH12 : (0 <= q)) (PreH13 : (q < 64)) (PreH14 : (cp <> 0)) (PreH15 : (p <> 0)) (PreH16 : (run <> 0)) (PreH17 : ((Z.land auth 64) <> 0)) (PreH18 : (parent = q)) (PreH19 : (dest0 <> q)) (PreH20 : (class0 <= 16)) (PreH21 : (dp = 0)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_124 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : ((grant_rights (auth) (right0)) <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (1 <= UINT_MAX)) (PreH6 : (right0 >= 0)) (PreH7 : ((grant_rights (auth) (right0)) >= 0)) (PreH8 : (class0 >= 0)) (PreH9 : (1 >= 0)) (PreH10 : (class0 <= 16)) (PreH11 : (dest0 < 64)) (PreH12 : (dp <> 0)) (PreH13 : (retval = 0)) (PreH14 : (dest0 < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (dest0 <> q)) (PreH23 : (class0 <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (class0 = 11)) (PreH27 : (oldright = auth)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (auth) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_125 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH5 : (class0 <= UINT_MAX)) (PreH6 : (1 <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (right0 >= 0)) (PreH9 : ((grant_rights (oldright) (right0)) >= 0)) (PreH10 : (class0 >= 0)) (PreH11 : (1 >= 0)) (PreH12 : (class0 <= 16)) (PreH13 : (dest0 < 64)) (PreH14 : (dp <> 0)) (PreH15 : (retval = 0)) (PreH16 : (dest0 < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (dest0 <> q)) (PreH25 : (class0 <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (class0 <> 11)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_safety_wit_126 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH5 : (class0 <= UINT_MAX)) (PreH6 : (1 <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (right0 >= 0)) (PreH9 : ((grant_rights (oldright) (right0)) >= 0)) (PreH10 : (class0 >= 0)) (PreH11 : (1 >= 0)) (PreH12 : (class0 <= 16)) (PreH13 : (dest0 < 64)) (PreH14 : (dp <> 0)) (PreH15 : (retval = 0)) (PreH16 : (dest0 < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (dest0 <> q)) (PreH25 : (class0 <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p <> dp)) ,
  ((( &( "i" ) )) # UChar  |-> retval)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ False ”
.

Definition grant_cspace_cap_entail_wit_1_1 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (destTask_Prio_pre <> q)) (PreH13 : (cap_Class_pre <= 16)) (PreH14 : (dp <> 0)) (PreH15 : (p <> dp)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p <> dp) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (oldright <= UINT_MAX)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (cap_Right_pre <= UINT_MAX)) (PreH4 : (cap_Class_pre <= UINT_MAX)) (PreH5 : (oldright >= 0)) (PreH6 : (auth >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent = q)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) (PreH23 : (p <> dp)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_1_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (oldright <= UINT_MAX)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (cap_Right_pre <= UINT_MAX)) (PreH4 : (cap_Class_pre <= UINT_MAX)) (PreH5 : (oldright >= 0)) (PreH6 : (auth >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent = q)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) (PreH23 : (p <> dp)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_2 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (destTask_Prio_pre <> q)) (PreH13 : (cap_Class_pre <= 16)) (PreH14 : (dp <> 0)) (PreH15 : (p = dp)) (PreH16 : (cap_Class_pre <> 11)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (oldright <= UINT_MAX)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (cap_Right_pre <= UINT_MAX)) (PreH4 : (cap_Class_pre <= UINT_MAX)) (PreH5 : (oldright >= 0)) (PreH6 : (auth >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent = q)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) (PreH23 : (p = dp)) (PreH24 : (cap_Class_pre <> 11)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_2_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (oldright <= UINT_MAX)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (cap_Right_pre <= UINT_MAX)) (PreH4 : (cap_Class_pre <= UINT_MAX)) (PreH5 : (oldright >= 0)) (PreH6 : (auth >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent = q)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) (PreH23 : (p = dp)) (PreH24 : (cap_Class_pre <> 11)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_3 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (destTask_Prio_pre <> q)) (PreH13 : (cap_Class_pre <= 16)) (PreH14 : (dp <> 0)) (PreH15 : (p = dp)) (PreH16 : (cap_Class_pre = 11)) (PreH17 : (oldright = auth)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (oldright <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (oldright >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent = q)) (PreH18 : (destTask_Prio_pre <> q)) (PreH19 : (cap_Class_pre <= 16)) (PreH20 : (dp <> 0)) (PreH21 : (p = dp)) (PreH22 : (cap_Class_pre = 11)) (PreH23 : (oldright = auth)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_3_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (oldright <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (oldright >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent = q)) (PreH18 : (destTask_Prio_pre <> q)) (PreH19 : (cap_Class_pre <= 16)) (PreH20 : (dp <> 0)) (PreH21 : (p = dp)) (PreH22 : (cap_Class_pre = 11)) (PreH23 : (oldright = auth)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_4 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (destTask_Prio_pre <> q)) (PreH13 : (cap_Class_pre <= 16)) (PreH14 : (dp = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (auth >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent = q)) (PreH18 : (destTask_Prio_pre <> q)) (PreH19 : (cap_Class_pre <= 16)) (PreH20 : (dp = 0)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_4_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (auth >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent = q)) (PreH18 : (destTask_Prio_pre <> q)) (PreH19 : (cap_Class_pre <= 16)) (PreH20 : (dp = 0)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (destTask_Prio_pre = q)) (PreH13 : (dp = p)) (PreH14 : (cap_Class_pre <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p = dp)) (PreH17 : (cap_Class_pre <> 11)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_1_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (destTask_Prio_pre = q)) (PreH13 : (dp = p)) (PreH14 : (cap_Class_pre <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p = dp)) (PreH17 : (cap_Class_pre = 11)) (PreH18 : (oldright = auth)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_1_7 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent = q)) (PreH12 : (cap_Class_pre > 16)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (auth >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent = q)) (PreH18 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_7_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (auth >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent = q)) (PreH18 : (cap_Class_pre > 16)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_8 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run = 0)) (PreH10 : (destTask_Prio_pre <> q)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (dp <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (oldright <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (oldright >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run = 0)) (PreH16 : (destTask_Prio_pre <> q)) (PreH17 : (cap_Class_pre <= 16)) (PreH18 : (dp <> 0)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_8_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (oldright <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (oldright >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run = 0)) (PreH16 : (destTask_Prio_pre <> q)) (PreH17 : (cap_Class_pre <= 16)) (PreH18 : (dp <> 0)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_9 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run = 0)) (PreH10 : (destTask_Prio_pre <> q)) (PreH11 : (cap_Class_pre <= 16)) (PreH12 : (dp = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (cap_Right_pre <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) (PreH4 : (cap_Class_pre >= 0)) (PreH5 : (destTask_Prio_pre = dest0)) (PreH6 : (cap_Class_pre = class0)) (PreH7 : (cap_Right_pre = right0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= q)) (PreH10 : (q < 64)) (PreH11 : (cp <> 0)) (PreH12 : (p <> 0)) (PreH13 : (run = 0)) (PreH14 : (destTask_Prio_pre <> q)) (PreH15 : (cap_Class_pre <= 16)) (PreH16 : (dp = 0)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_9_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (cap_Right_pre <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) (PreH4 : (cap_Class_pre >= 0)) (PreH5 : (destTask_Prio_pre = dest0)) (PreH6 : (cap_Class_pre = class0)) (PreH7 : (cap_Right_pre = right0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= q)) (PreH10 : (q < 64)) (PreH11 : (cp <> 0)) (PreH12 : (p <> 0)) (PreH13 : (run = 0)) (PreH14 : (destTask_Prio_pre <> q)) (PreH15 : (cap_Class_pre <= 16)) (PreH16 : (dp = 0)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run = 0)) (PreH10 : (destTask_Prio_pre = q)) (PreH11 : (dp = p)) (PreH12 : (cap_Class_pre <= 16)) (PreH13 : (dp <> 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_1_11 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run = 0)) (PreH10 : (cap_Class_pre > 16)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (cap_Right_pre <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) (PreH4 : (cap_Class_pre >= 0)) (PreH5 : (destTask_Prio_pre = dest0)) (PreH6 : (cap_Class_pre = class0)) (PreH7 : (cap_Right_pre = right0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= q)) (PreH10 : (q < 64)) (PreH11 : (cp <> 0)) (PreH12 : (p <> 0)) (PreH13 : (run = 0)) (PreH14 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_11_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (cap_Right_pre <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) (PreH4 : (cap_Class_pre >= 0)) (PreH5 : (destTask_Prio_pre = dest0)) (PreH6 : (cap_Class_pre = class0)) (PreH7 : (cap_Right_pre = right0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= q)) (PreH10 : (q < 64)) (PreH11 : (cp <> 0)) (PreH12 : (p <> 0)) (PreH13 : (run = 0)) (PreH14 : (cap_Class_pre > 16)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_12 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) <> 0)) (PreH11 : (parent <> q)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent <> q) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (auth >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent <> q)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_12_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (auth >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent <> q)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_13 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p <> 0)) (PreH9 : (run <> 0)) (PreH10 : ((Z.land auth 64) = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (auth >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) = 0)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_13_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (cap_Right_pre <= UINT_MAX)) (PreH3 : (cap_Class_pre <= UINT_MAX)) (PreH4 : (auth >= 0)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) = 0)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_14 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= q)) (PreH6 : (q < 64)) (PreH7 : (cp <> 0)) (PreH8 : (p = 0)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (cap_Right_pre <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) (PreH4 : (cap_Class_pre >= 0)) (PreH5 : (destTask_Prio_pre = dest0)) (PreH6 : (cap_Class_pre = class0)) (PreH7 : (cap_Right_pre = right0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= q)) (PreH10 : (q < 64)) (PreH11 : (cp <> 0)) (PreH12 : (p = 0)) ,
  TT && emp 
|--
  “ (0 <= destTask_Prio_pre) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_14_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (cap_Right_pre <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) (PreH4 : (cap_Class_pre >= 0)) (PreH5 : (destTask_Prio_pre = dest0)) (PreH6 : (cap_Class_pre = class0)) (PreH7 : (cap_Right_pre = right0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= q)) (PreH10 : (q < 64)) (PreH11 : (cp <> 0)) (PreH12 : (p = 0)) ,
  (0 <= destTask_Prio_pre)
.

Definition grant_cspace_cap_entail_wit_1_15 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (PreH1 : (destTask_Prio_pre = dest0)) (PreH2 : (cap_Class_pre = class0)) (PreH3 : (cap_Right_pre = right0)) (PreH4 : (destTask_Prio_pre >= 63)) ,
  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre >= 63) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (PreH1 : (cap_Right_pre <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) (PreH4 : (cap_Class_pre >= 0)) (PreH5 : (destTask_Prio_pre = dest0)) (PreH6 : (cap_Class_pre = class0)) (PreH7 : (cap_Right_pre = right0)) (PreH8 : (destTask_Prio_pre >= 63)) ,
  TT && emp 
|--
  “ (destTask_Prio_pre <= 255) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_1_15_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (PreH1 : (cap_Right_pre <= UINT_MAX)) (PreH2 : (cap_Class_pre <= UINT_MAX)) (PreH3 : (cap_Right_pre >= 0)) (PreH4 : (cap_Class_pre >= 0)) (PreH5 : (destTask_Prio_pre = dest0)) (PreH6 : (cap_Class_pre = class0)) (PreH7 : (cap_Right_pre = right0)) (PreH8 : (destTask_Prio_pre >= 63)) ,
  (destTask_Prio_pre <= 255)
.

Definition grant_cspace_cap_entail_wit_2_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (oldright <= UINT_MAX)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p <> dp) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_2_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (oldright <= UINT_MAX)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_2_3 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (oldright <= UINT_MAX)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (oldright >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent = q)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) (PreH23 : (p = dp)) (PreH24 : (cap_Class_pre = 11)) (PreH25 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_2_4 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (auth <= UINT_MAX)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (auth >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent = q)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_entail_wit_2_5 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (oldright <= UINT_MAX)) (PreH4 : (auth <= UINT_MAX)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (oldright >= 0)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre = q)) (PreH23 : (dp = p)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_2_6 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (oldright <= UINT_MAX)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (oldright >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent = q)) (PreH20 : (destTask_Prio_pre = q)) (PreH21 : (dp = p)) (PreH22 : (cap_Class_pre <= 16)) (PreH23 : (dp <> 0)) (PreH24 : (p = dp)) (PreH25 : (cap_Class_pre = 11)) (PreH26 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_2_7 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (auth <= UINT_MAX)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (auth >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent = q)) (PreH20 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_entail_wit_2_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (oldright <= UINT_MAX)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (oldright >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run = 0)) (PreH18 : (destTask_Prio_pre <> q)) (PreH19 : (cap_Class_pre <= 16)) (PreH20 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_2_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (cap_Right_pre <= UINT_MAX)) (PreH4 : (cap_Class_pre <= UINT_MAX)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run = 0)) (PreH16 : (destTask_Prio_pre <> q)) (PreH17 : (cap_Class_pre <= 16)) (PreH18 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
.

Definition grant_cspace_cap_entail_wit_2_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (oldcur: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (oldright <= UINT_MAX)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (oldright >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run = 0)) (PreH18 : (destTask_Prio_pre = q)) (PreH19 : (dp = p)) (PreH20 : (cap_Class_pre <= 16)) (PreH21 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_2_11 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (cap_Right_pre <= UINT_MAX)) (PreH4 : (cap_Class_pre <= UINT_MAX)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run = 0)) (PreH16 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_entail_wit_2_12 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (auth <= UINT_MAX)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (auth >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) <> 0)) (PreH19 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent <> q) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_entail_wit_2_13 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (auth <= UINT_MAX)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (auth >= 0)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run <> 0)) (PreH18 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_entail_wit_2_14 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldcur: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (cap_Right_pre <= UINT_MAX)) (PreH4 : (cap_Class_pre <= UINT_MAX)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> oldcur)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
.

Definition grant_cspace_cap_entail_wit_2_15 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (PreH1 : (0 <= destTask_Prio_pre)) (PreH2 : (destTask_Prio_pre <= 255)) (PreH3 : (cap_Right_pre <= UINT_MAX)) (PreH4 : (cap_Class_pre <= UINT_MAX)) (PreH5 : (cap_Right_pre >= 0)) (PreH6 : (cap_Class_pre >= 0)) (PreH7 : (destTask_Prio_pre = dest0)) (PreH8 : (cap_Class_pre = class0)) (PreH9 : (cap_Right_pre = right0)) (PreH10 : (destTask_Prio_pre >= 63)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
|--
  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre >= 63) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
.

Definition grant_cspace_cap_entail_wit_3_1 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p <> dp) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p <> dp)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_1_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p <> dp)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_1_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p <> dp)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_3_2 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre <> 11)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_2_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre <> 11)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_2_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre <> 11)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_3_3 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (cap_Class_pre = 11)) (PreH27 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (cap_Class_pre = 11)) (PreH27 : (oldright = auth)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_3_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (cap_Class_pre = 11)) (PreH27 : (oldright = auth)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_3_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (cap_Class_pre = 11)) (PreH27 : (oldright = auth)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_3_4 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_4_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_4_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_3_5 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (cap_Class_pre <> 11)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_5_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (cap_Class_pre <> 11)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_5_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (auth <= UINT_MAX)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (oldright >= 0)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (cap_Class_pre <> 11)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_3_6 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre = q)) (PreH23 : (dp = p)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (cap_Class_pre = 11)) (PreH28 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre = q)) (PreH23 : (dp = p)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (cap_Class_pre = 11)) (PreH28 : (oldright = auth)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_6_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre = q)) (PreH23 : (dp = p)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (cap_Class_pre = 11)) (PreH28 : (oldright = auth)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_6_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (destTask_Prio_pre = q)) (PreH23 : (dp = p)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (cap_Class_pre = 11)) (PreH28 : (oldright = auth)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_3_7 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_7_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (cap_Class_pre > 16)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_7_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (cap_Class_pre > 16)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_3_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_3_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run = 0)) (PreH18 : (destTask_Prio_pre <> q)) (PreH19 : (cap_Class_pre <= 16)) (PreH20 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
.

Definition grant_cspace_cap_entail_wit_3_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (oldright <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (oldright >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (destTask_Prio_pre = q)) (PreH21 : (dp = p)) (PreH22 : (cap_Class_pre <= 16)) (PreH23 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_3_11 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p <> 0)) (PreH17 : (run = 0)) (PreH18 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_entail_wit_3_12 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent <> q) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent <> q)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_12_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent <> q)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_12_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent <> q)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_3_13 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) = 0)) ,
  TT && emp 
|--
  “ (run <= 255) ” 
  &&  “ (0 <= run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_3_13_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) = 0)) ,
  (run <= 255)
.

Definition grant_cspace_cap_entail_wit_3_13_split_goal_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p <> 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (auth <= UINT_MAX)) (PreH6 : (cap_Right_pre <= UINT_MAX)) (PreH7 : (cap_Class_pre <= UINT_MAX)) (PreH8 : (auth >= 0)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) = 0)) ,
  (0 <= run)
.

Definition grant_cspace_cap_entail_wit_4_1 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p <> dp) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p <> dp)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_1_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p <> dp)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_4_2 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p = dp)) (PreH30 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p = dp)) (PreH30 : (cap_Class_pre <> 11)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_2_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p = dp)) (PreH30 : (cap_Class_pre <> 11)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_4_3 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (oldright >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre = 11)) (PreH29 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (oldright >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre = 11)) (PreH29 : (oldright = auth)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_3_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (oldright >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (cap_Class_pre = 11)) (PreH29 : (oldright = auth)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_4_4 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp = 0)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_4_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp = 0)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_4_5 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre = q)) (PreH27 : (dp = p)) (PreH28 : (cap_Class_pre <= 16)) (PreH29 : (dp <> 0)) (PreH30 : (p = dp)) (PreH31 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre = q)) (PreH27 : (dp = p)) (PreH28 : (cap_Class_pre <= 16)) (PreH29 : (dp <> 0)) (PreH30 : (p = dp)) (PreH31 : (cap_Class_pre <> 11)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_5_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (auth <= UINT_MAX)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (oldright >= 0)) (PreH12 : (auth >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre = q)) (PreH27 : (dp = p)) (PreH28 : (cap_Class_pre <= 16)) (PreH29 : (dp <> 0)) (PreH30 : (p = dp)) (PreH31 : (cap_Class_pre <> 11)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_4_6 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (oldright >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (cap_Class_pre = 11)) (PreH30 : (oldright = auth)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (oldright >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (cap_Class_pre = 11)) (PreH30 : (oldright = auth)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_6_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (oldright >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (cap_Class_pre = 11)) (PreH30 : (oldright = auth)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_4_7 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_7_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (cap_Class_pre > 16)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_4_8 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (oldright >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_4_9 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (destTask_Prio_pre <> q)) (PreH21 : (cap_Class_pre <= 16)) (PreH22 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
.

Definition grant_cspace_cap_entail_wit_4_10 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (oldright <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (oldright >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (destTask_Prio_pre = q)) (PreH23 : (dp = p)) (PreH24 : (cap_Class_pre <= 16)) (PreH25 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
.

Definition grant_cspace_cap_entail_wit_4_11 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (cap_Right_pre <= UINT_MAX)) (PreH8 : (cap_Class_pre <= UINT_MAX)) (PreH9 : (cap_Right_pre >= 0)) (PreH10 : (cap_Class_pre >= 0)) (PreH11 : (destTask_Prio_pre = dest0)) (PreH12 : (cap_Class_pre = class0)) (PreH13 : (cap_Right_pre = right0)) (PreH14 : (destTask_Prio_pre < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (cap_Class_pre > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_entail_wit_4_12 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent <> q)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent <> q) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent <> q)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_12_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent <> q)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_4_13 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (auth <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "i" ) )) # UChar  |->_)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) = 0)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (run) (32)) = run) ”
  &&  emp
).

Definition grant_cspace_cap_entail_wit_4_13_split_goal_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (0 <= run)) (PreH2 : (run <= 255)) (PreH3 : (p <> 0)) (PreH4 : (destTask_Prio_pre < 63)) (PreH5 : (0 <= destTask_Prio_pre)) (PreH6 : (destTask_Prio_pre <= 255)) (PreH7 : (auth <= UINT_MAX)) (PreH8 : (cap_Right_pre <= UINT_MAX)) (PreH9 : (cap_Class_pre <= UINT_MAX)) (PreH10 : (auth >= 0)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) = 0)) ,
  ((unsigned_last_nbits (run) (32)) = run)
.

Definition grant_cspace_cap_entail_wit_5_1 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (class0 > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_1_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (cap_Class_pre > 16)) ,
  TT && emp 
|--
  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_2 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run = 0)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run = 0)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_2_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run = 0)) (PreH24 : (destTask_Prio_pre = q)) (PreH25 : (dp = p)) (PreH26 : (cap_Class_pre <= 16)) (PreH27 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_3 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_3_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (cap_Right_pre <= UINT_MAX)) (PreH10 : (cap_Class_pre <= UINT_MAX)) (PreH11 : (cap_Right_pre >= 0)) (PreH12 : (cap_Class_pre >= 0)) (PreH13 : (destTask_Prio_pre = dest0)) (PreH14 : (cap_Class_pre = class0)) (PreH15 : (cap_Right_pre = right0)) (PreH16 : (destTask_Prio_pre < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run = 0)) (PreH22 : (destTask_Prio_pre <> q)) (PreH23 : (cap_Class_pre <= 16)) (PreH24 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_4 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run = 0)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run = 0)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_4_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run = 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run = 0)) (PreH24 : (destTask_Prio_pre <> q)) (PreH25 : (cap_Class_pre <= 16)) (PreH26 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_5 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p <> dp)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p <> dp) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p <> dp)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_5_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p <> dp)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_6 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p = dp)) (PreH34 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p = dp)) (PreH34 : (cap_Class_pre <> 11)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_6_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p = dp)) (PreH34 : (cap_Class_pre <> 11)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_7 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp = 0)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp = 0)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_7_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp = 0)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_8 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre = q)) (PreH31 : (dp = p)) (PreH32 : (cap_Class_pre <= 16)) (PreH33 : (dp <> 0)) (PreH34 : (p = dp)) (PreH35 : (cap_Class_pre <> 11)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 <> 11) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre = q)) (PreH31 : (dp = p)) (PreH32 : (cap_Class_pre <= 16)) (PreH33 : (dp <> 0)) (PreH34 : (p = dp)) (PreH35 : (cap_Class_pre <> 11)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_8_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (auth <= UINT_MAX)) (PreH13 : (cap_Right_pre <= UINT_MAX)) (PreH14 : (cap_Class_pre <= UINT_MAX)) (PreH15 : (oldright >= 0)) (PreH16 : (auth >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre = q)) (PreH31 : (dp = p)) (PreH32 : (cap_Class_pre <= 16)) (PreH33 : (dp <> 0)) (PreH34 : (p = dp)) (PreH35 : (cap_Class_pre <> 11)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_9 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (cap_Class_pre > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (class0 > 16) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (cap_Class_pre > 16)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_9_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (cap_Class_pre > 16)) ,
  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_10 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (oldright >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre = q)) (PreH29 : (dp = p)) (PreH30 : (cap_Class_pre <= 16)) (PreH31 : (dp <> 0)) (PreH32 : (p = dp)) (PreH33 : (cap_Class_pre = 11)) (PreH34 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (auth >= 0)) (PreH3 : (parent = q)) (PreH4 : ((Z.land auth 64) <> 0)) (PreH5 : (run <> 0)) (PreH6 : ((unsigned_last_nbits (run) (32)) = run)) (PreH7 : (0 <= run)) (PreH8 : (run <= 255)) (PreH9 : (p <> 0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= destTask_Prio_pre)) (PreH12 : (destTask_Prio_pre <= 255)) (PreH13 : (oldright <= UINT_MAX)) (PreH14 : (cap_Right_pre <= UINT_MAX)) (PreH15 : (cap_Class_pre <= UINT_MAX)) (PreH16 : (oldright >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre = q)) (PreH31 : (dp = p)) (PreH32 : (cap_Class_pre <= 16)) (PreH33 : (dp <> 0)) (PreH34 : (p = dp)) (PreH35 : (cap_Class_pre = 11)) (PreH36 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_10_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (auth >= 0)) (PreH3 : (parent = q)) (PreH4 : ((Z.land auth 64) <> 0)) (PreH5 : (run <> 0)) (PreH6 : ((unsigned_last_nbits (run) (32)) = run)) (PreH7 : (0 <= run)) (PreH8 : (run <= 255)) (PreH9 : (p <> 0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= destTask_Prio_pre)) (PreH12 : (destTask_Prio_pre <= 255)) (PreH13 : (oldright <= UINT_MAX)) (PreH14 : (cap_Right_pre <= UINT_MAX)) (PreH15 : (cap_Class_pre <= UINT_MAX)) (PreH16 : (oldright >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre = q)) (PreH31 : (dp = p)) (PreH32 : (cap_Class_pre <= 16)) (PreH33 : (dp <> 0)) (PreH34 : (p = dp)) (PreH35 : (cap_Class_pre = 11)) (PreH36 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_5_11 := 
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (parent = q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (oldright <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (oldright >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent = q)) (PreH28 : (destTask_Prio_pre <> q)) (PreH29 : (cap_Class_pre <= 16)) (PreH30 : (dp <> 0)) (PreH31 : (p = dp)) (PreH32 : (cap_Class_pre = 11)) (PreH33 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> destTask_Prio_pre)
  **  ((( &( "cap_Class" ) )) # UInt  |-> cap_Class_pre)
  **  ((( &( "cap_Right" ) )) # UInt  |-> cap_Right_pre)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
) \/
(
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (auth >= 0)) (PreH3 : (parent = q)) (PreH4 : ((Z.land auth 64) <> 0)) (PreH5 : (run <> 0)) (PreH6 : ((unsigned_last_nbits (run) (32)) = run)) (PreH7 : (0 <= run)) (PreH8 : (run <= 255)) (PreH9 : (p <> 0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= destTask_Prio_pre)) (PreH12 : (destTask_Prio_pre <= 255)) (PreH13 : (oldright <= UINT_MAX)) (PreH14 : (cap_Right_pre <= UINT_MAX)) (PreH15 : (cap_Class_pre <= UINT_MAX)) (PreH16 : (oldright >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p = dp)) (PreH34 : (cap_Class_pre = 11)) (PreH35 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
).

Definition grant_cspace_cap_entail_wit_5_11_split_goal_spatial := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (auth <= UINT_MAX)) (PreH2 : (auth >= 0)) (PreH3 : (parent = q)) (PreH4 : ((Z.land auth 64) <> 0)) (PreH5 : (run <> 0)) (PreH6 : ((unsigned_last_nbits (run) (32)) = run)) (PreH7 : (0 <= run)) (PreH8 : (run <= 255)) (PreH9 : (p <> 0)) (PreH10 : (destTask_Prio_pre < 63)) (PreH11 : (0 <= destTask_Prio_pre)) (PreH12 : (destTask_Prio_pre <= 255)) (PreH13 : (oldright <= UINT_MAX)) (PreH14 : (cap_Right_pre <= UINT_MAX)) (PreH15 : (cap_Class_pre <= UINT_MAX)) (PreH16 : (oldright >= 0)) (PreH17 : (cap_Right_pre >= 0)) (PreH18 : (cap_Class_pre >= 0)) (PreH19 : (destTask_Prio_pre = dest0)) (PreH20 : (cap_Class_pre = class0)) (PreH21 : (cap_Right_pre = right0)) (PreH22 : (destTask_Prio_pre < 63)) (PreH23 : (0 <= q)) (PreH24 : (q < 64)) (PreH25 : (cp <> 0)) (PreH26 : (p <> 0)) (PreH27 : (run <> 0)) (PreH28 : ((Z.land auth 64) <> 0)) (PreH29 : (parent = q)) (PreH30 : (destTask_Prio_pre <> q)) (PreH31 : (cap_Class_pre <= 16)) (PreH32 : (dp <> 0)) (PreH33 : (p = dp)) (PreH34 : (cap_Class_pre = 11)) (PreH35 : (oldright = auth)) ,
  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
|--
  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
.

Definition grant_cspace_cap_entail_wit_6_1 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run = 0)) (PreH9 : (class0 > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |-> retval)
|--
  “ (right0 <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (class0 > 16) ” 
  &&  “ (retval = 11) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (class0 > 16) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_entail_wit_6_2 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_2: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (p <> 0)) (PreH4 : (retval_2 = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run = 0)) (PreH11 : (dest0 = q)) (PreH12 : (dp = p)) (PreH13 : (class0 <= 16)) (PreH14 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |-> retval_2)
|--
  “ (right0 <= UINT_MAX) ” 
  &&  “ ((grant_rights (oldright) (right0)) <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (1 <= UINT_MAX) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ ((grant_rights (oldright) (right0)) >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (p <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_2)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_entail_wit_6_3 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_3: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (0 = 0)) (PreH4 : (retval_3 = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run = 0)) (PreH11 : (dest0 <> q)) (PreH12 : (class0 <= 16)) (PreH13 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |-> retval_3)
|--
  “ (right0 <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (retval_3 = 11) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_3)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_entail_wit_6_4 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_4: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp <> 0)) (PreH4 : (retval_4 = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run = 0)) (PreH11 : (dest0 <> q)) (PreH12 : (class0 <= 16)) (PreH13 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((( &( "i" ) )) # UChar  |-> retval_4)
|--
  “ (right0 <= UINT_MAX) ” 
  &&  “ ((grant_rights (oldright) (right0)) <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (1 <= UINT_MAX) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ ((grant_rights (oldright) (right0)) >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_4)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_entail_wit_6_5 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (retval_5: Z) (PreH1 : (class0 > 16)) (PreH2 : (retval_5 = 11)) (PreH3 : (dest0 < 63)) (PreH4 : (0 <= q)) (PreH5 : (q < 64)) (PreH6 : (cp <> 0)) (PreH7 : (p <> 0)) (PreH8 : (run <> 0)) (PreH9 : ((Z.land auth 64) <> 0)) (PreH10 : (parent = q)) (PreH11 : (class0 > 16)) ,
  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |-> retval_5)
|--
  “ (auth <= UINT_MAX) ” 
  &&  “ (right0 <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (class0 > 16) ” 
  &&  “ (retval_5 = 11) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (class0 > 16) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_5)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_entail_wit_6_6 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_6: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp <> 0)) (PreH4 : (retval_6 = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 = q)) (PreH14 : (dp = p)) (PreH15 : (class0 <= 16)) (PreH16 : (dp <> 0)) (PreH17 : (p = dp)) (PreH18 : (class0 = 11)) (PreH19 : (oldright = auth)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (auth) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "i" ) )) # UChar  |-> retval_6)
|--
  “ (right0 <= UINT_MAX) ” 
  &&  “ ((grant_rights (auth) (right0)) <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (1 <= UINT_MAX) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ ((grant_rights (auth) (right0)) >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (retval_6 = 0) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_6)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (auth) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_entail_wit_6_7 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_7: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp <> 0)) (PreH4 : (retval_7 = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 = q)) (PreH14 : (dp = p)) (PreH15 : (class0 <= 16)) (PreH16 : (dp <> 0)) (PreH17 : (p = dp)) (PreH18 : (class0 <> 11)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |-> retval_7)
|--
  “ (auth <= UINT_MAX) ” 
  &&  “ (right0 <= UINT_MAX) ” 
  &&  “ ((grant_rights (oldright) (right0)) <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (1 <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ ((grant_rights (oldright) (right0)) >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (retval_7 = 0) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 <> 11) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_7)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_entail_wit_6_8 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_8: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (0 = 0)) (PreH4 : (retval_8 = 11)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 <> q)) (PreH14 : (class0 <= 16)) (PreH15 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |-> retval_8)
|--
  “ (auth <= UINT_MAX) ” 
  &&  “ (right0 <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (retval_8 = 11) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp = 0) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_8)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_entail_wit_6_9 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_9: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp <> 0)) (PreH4 : (retval_9 = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 <> q)) (PreH14 : (class0 <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p = dp)) (PreH17 : (class0 = 11)) (PreH18 : (oldright = auth)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (auth) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((( &( "i" ) )) # UChar  |-> retval_9)
|--
  “ (right0 <= UINT_MAX) ” 
  &&  “ ((grant_rights (auth) (right0)) <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (1 <= UINT_MAX) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ ((grant_rights (auth) (right0)) >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (retval_9 = 0) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_9)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (auth) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_entail_wit_6_10 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_10: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp <> 0)) (PreH4 : (retval_10 = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 <> q)) (PreH14 : (class0 <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p = dp)) (PreH17 : (class0 <> 11)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |-> retval_10)
|--
  “ (auth <= UINT_MAX) ” 
  &&  “ (right0 <= UINT_MAX) ” 
  &&  “ ((grant_rights (oldright) (right0)) <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (1 <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ ((grant_rights (oldright) (right0)) >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (retval_10 = 0) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 <> 11) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_10)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_entail_wit_6_11 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval_11: Z) (PreH1 : (class0 <= 16)) (PreH2 : (dest0 < 64)) (PreH3 : (dp <> 0)) (PreH4 : (retval_11 = 0)) (PreH5 : (dest0 < 63)) (PreH6 : (0 <= q)) (PreH7 : (q < 64)) (PreH8 : (cp <> 0)) (PreH9 : (p <> 0)) (PreH10 : (run <> 0)) (PreH11 : ((Z.land auth 64) <> 0)) (PreH12 : (parent = q)) (PreH13 : (dest0 <> q)) (PreH14 : (class0 <= 16)) (PreH15 : (dp <> 0)) (PreH16 : (p <> dp)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "i" ) )) # UChar  |-> retval_11)
|--
  “ (auth <= UINT_MAX) ” 
  &&  “ (right0 <= UINT_MAX) ” 
  &&  “ ((grant_rights (oldright) (right0)) <= UINT_MAX) ” 
  &&  “ (class0 <= UINT_MAX) ” 
  &&  “ (1 <= UINT_MAX) ” 
  &&  “ (auth >= 0) ” 
  &&  “ (right0 >= 0) ” 
  &&  “ ((grant_rights (oldright) (right0)) >= 0) ” 
  &&  “ (class0 >= 0) ” 
  &&  “ (1 >= 0) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dest0 < 64) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (retval_11 = 0) ” 
  &&  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p <> dp) ”
  &&  ((( &( "i" ) )) # UChar  |-> retval_11)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "destTask_Prio" ) )) # UChar  |-> dest0)
  **  ((( &( "cap_Class" ) )) # UInt  |-> class0)
  **  ((( &( "cap_Right" ) )) # UInt  |-> right0)
  **  ((( &( "pCSpace" ) )) # Ptr  |-> p)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_return_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (parent <> q)) (PreH2 : ((Z.land auth 64) <> 0)) (PreH3 : (run <> 0)) (PreH4 : ((unsigned_last_nbits (run) (32)) = run)) (PreH5 : (0 <= run)) (PreH6 : (run <= 255)) (PreH7 : (p <> 0)) (PreH8 : (destTask_Prio_pre < 63)) (PreH9 : (0 <= destTask_Prio_pre)) (PreH10 : (destTask_Prio_pre <= 255)) (PreH11 : (auth <= UINT_MAX)) (PreH12 : (cap_Right_pre <= UINT_MAX)) (PreH13 : (cap_Class_pre <= UINT_MAX)) (PreH14 : (auth >= 0)) (PreH15 : (cap_Right_pre >= 0)) (PreH16 : (cap_Class_pre >= 0)) (PreH17 : (destTask_Prio_pre = dest0)) (PreH18 : (cap_Class_pre = class0)) (PreH19 : (cap_Right_pre = right0)) (PreH20 : (destTask_Prio_pre < 63)) (PreH21 : (0 <= q)) (PreH22 : (q < 64)) (PreH23 : (cp <> 0)) (PreH24 : (p <> 0)) (PreH25 : (run <> 0)) (PreH26 : ((Z.land auth 64) <> 0)) (PreH27 : (parent <> q)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent <> q) ” 
  &&  “ (252 = 252) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_return_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : ((Z.land auth 64) = 0)) (PreH2 : (run <> 0)) (PreH3 : ((unsigned_last_nbits (run) (32)) = run)) (PreH4 : (0 <= run)) (PreH5 : (run <= 255)) (PreH6 : (p <> 0)) (PreH7 : (destTask_Prio_pre < 63)) (PreH8 : (0 <= destTask_Prio_pre)) (PreH9 : (destTask_Prio_pre <= 255)) (PreH10 : (auth <= UINT_MAX)) (PreH11 : (cap_Right_pre <= UINT_MAX)) (PreH12 : (cap_Class_pre <= UINT_MAX)) (PreH13 : (auth >= 0)) (PreH14 : (cap_Right_pre >= 0)) (PreH15 : (cap_Class_pre >= 0)) (PreH16 : (destTask_Prio_pre = dest0)) (PreH17 : (cap_Class_pre = class0)) (PreH18 : (cap_Right_pre = right0)) (PreH19 : (destTask_Prio_pre < 63)) (PreH20 : (0 <= q)) (PreH21 : (q < 64)) (PreH22 : (cp <> 0)) (PreH23 : (p <> 0)) (PreH24 : (run <> 0)) (PreH25 : ((Z.land auth 64) = 0)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) = 0) ” 
  &&  “ (252 = 252) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_return_wit_3 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : (class0 <= UINT_MAX)) (PreH4 : (right0 >= 0)) (PreH5 : (class0 >= 0)) (PreH6 : (class0 > 16)) (PreH7 : (retval = 11)) (PreH8 : (dest0 < 63)) (PreH9 : (0 <= q)) (PreH10 : (q < 64)) (PreH11 : (cp <> 0)) (PreH12 : (p <> 0)) (PreH13 : (run = 0)) (PreH14 : (class0 > 16)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (class0 > 16) ” 
  &&  “ (11 = 11) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_return_wit_4 := 
forall (right0: Z) (class0: Z) (dest0: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : (class0 <= UINT_MAX)) (PreH4 : (right0 >= 0)) (PreH5 : (class0 >= 0)) (PreH6 : (class0 <= 16)) (PreH7 : (dest0 < 64)) (PreH8 : (retval = 11)) (PreH9 : (dest0 < 63)) (PreH10 : (0 <= q)) (PreH11 : (q < 64)) (PreH12 : (cp <> 0)) (PreH13 : (p <> 0)) (PreH14 : (run = 0)) (PreH15 : (dest0 <> q)) (PreH16 : (class0 <= 16)) (PreH17 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp = 0) ” 
  &&  “ (11 = 11) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
.

Definition grant_cspace_cap_return_wit_5 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (auth >= 0)) (PreH6 : (right0 >= 0)) (PreH7 : (class0 >= 0)) (PreH8 : (class0 > 16)) (PreH9 : (retval = 11)) (PreH10 : (dest0 < 63)) (PreH11 : (0 <= q)) (PreH12 : (q < 64)) (PreH13 : (cp <> 0)) (PreH14 : (p <> 0)) (PreH15 : (run <> 0)) (PreH16 : ((Z.land auth 64) <> 0)) (PreH17 : (parent = q)) (PreH18 : (class0 > 16)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (class0 > 16) ” 
  &&  “ (11 = 11) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_return_wit_6 := 
forall (right0: Z) (class0: Z) (dest0: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (auth >= 0)) (PreH6 : (right0 >= 0)) (PreH7 : (class0 >= 0)) (PreH8 : (class0 <= 16)) (PreH9 : (dest0 < 64)) (PreH10 : (retval = 11)) (PreH11 : (dest0 < 63)) (PreH12 : (0 <= q)) (PreH13 : (q < 64)) (PreH14 : (cp <> 0)) (PreH15 : (p <> 0)) (PreH16 : (run <> 0)) (PreH17 : ((Z.land auth 64) <> 0)) (PreH18 : (parent = q)) (PreH19 : (dest0 <> q)) (PreH20 : (class0 <= 16)) (PreH21 : (dp = 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> 0)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp = 0) ” 
  &&  “ (11 = 11) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_return_wit_7 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (1 <= UINT_MAX)) (PreH6 : (right0 >= 0)) (PreH7 : ((grant_rights (oldright) (right0)) >= 0)) (PreH8 : (class0 >= 0)) (PreH9 : (1 >= 0)) (PreH10 : (class0 <= 16)) (PreH11 : (dest0 < 64)) (PreH12 : (p <> 0)) (PreH13 : (retval = 0)) (PreH14 : (dest0 < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (dest0 = q)) (PreH21 : (dp = p)) (PreH22 : (class0 <= 16)) (PreH23 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> p)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
.

Definition grant_cspace_cap_return_wit_8 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (1 <= UINT_MAX)) (PreH6 : (right0 >= 0)) (PreH7 : ((grant_rights (oldright) (right0)) >= 0)) (PreH8 : (class0 >= 0)) (PreH9 : (1 >= 0)) (PreH10 : (class0 <= 16)) (PreH11 : (dest0 < 64)) (PreH12 : (dp <> 0)) (PreH13 : (retval = 0)) (PreH14 : (dest0 < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run = 0)) (PreH20 : (dest0 <> q)) (PreH21 : (class0 <= 16)) (PreH22 : (dp <> 0)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
.

Definition grant_cspace_cap_return_wit_9 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : ((grant_rights (auth) (right0)) <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (1 <= UINT_MAX)) (PreH6 : (right0 >= 0)) (PreH7 : ((grant_rights (auth) (right0)) >= 0)) (PreH8 : (class0 >= 0)) (PreH9 : (1 >= 0)) (PreH10 : (class0 <= 16)) (PreH11 : (dest0 < 64)) (PreH12 : (dp <> 0)) (PreH13 : (retval = 0)) (PreH14 : (dest0 < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (dest0 = q)) (PreH23 : (dp = p)) (PreH24 : (class0 <= 16)) (PreH25 : (dp <> 0)) (PreH26 : (p = dp)) (PreH27 : (class0 = 11)) (PreH28 : (oldright = auth)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (auth) (right0)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 = 11) ” 
  &&  “ (oldright = auth) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
.

Definition grant_cspace_cap_return_wit_10 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH5 : (class0 <= UINT_MAX)) (PreH6 : (1 <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (right0 >= 0)) (PreH9 : ((grant_rights (oldright) (right0)) >= 0)) (PreH10 : (class0 >= 0)) (PreH11 : (1 >= 0)) (PreH12 : (class0 <= 16)) (PreH13 : (dest0 < 64)) (PreH14 : (dp <> 0)) (PreH15 : (retval = 0)) (PreH16 : (dest0 < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (dest0 = q)) (PreH25 : (dp = p)) (PreH26 : (class0 <= 16)) (PreH27 : (dp <> 0)) (PreH28 : (p = dp)) (PreH29 : (class0 <> 11)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 <> 11) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
.

Definition grant_cspace_cap_return_wit_11 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (right0 <= UINT_MAX)) (PreH3 : ((grant_rights (auth) (right0)) <= UINT_MAX)) (PreH4 : (class0 <= UINT_MAX)) (PreH5 : (1 <= UINT_MAX)) (PreH6 : (right0 >= 0)) (PreH7 : ((grant_rights (auth) (right0)) >= 0)) (PreH8 : (class0 >= 0)) (PreH9 : (1 >= 0)) (PreH10 : (class0 <= 16)) (PreH11 : (dest0 < 64)) (PreH12 : (dp <> 0)) (PreH13 : (retval = 0)) (PreH14 : (dest0 < 63)) (PreH15 : (0 <= q)) (PreH16 : (q < 64)) (PreH17 : (cp <> 0)) (PreH18 : (p <> 0)) (PreH19 : (run <> 0)) (PreH20 : ((Z.land auth 64) <> 0)) (PreH21 : (parent = q)) (PreH22 : (dest0 <> q)) (PreH23 : (class0 <= 16)) (PreH24 : (dp <> 0)) (PreH25 : (p = dp)) (PreH26 : (class0 = 11)) (PreH27 : (oldright = auth)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (auth) (right0)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 = 11) ” 
  &&  “ (oldright = auth) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
.

Definition grant_cspace_cap_return_wit_12 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH5 : (class0 <= UINT_MAX)) (PreH6 : (1 <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (right0 >= 0)) (PreH9 : ((grant_rights (oldright) (right0)) >= 0)) (PreH10 : (class0 >= 0)) (PreH11 : (1 >= 0)) (PreH12 : (class0 <= 16)) (PreH13 : (dest0 < 64)) (PreH14 : (dp <> 0)) (PreH15 : (retval = 0)) (PreH16 : (dest0 < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (dest0 <> q)) (PreH25 : (class0 <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p = dp)) (PreH28 : (class0 <> 11)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 <> 11) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
.

Definition grant_cspace_cap_return_wit_13 := 
forall (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (auth <= UINT_MAX)) (PreH3 : (right0 <= UINT_MAX)) (PreH4 : ((grant_rights (oldright) (right0)) <= UINT_MAX)) (PreH5 : (class0 <= UINT_MAX)) (PreH6 : (1 <= UINT_MAX)) (PreH7 : (auth >= 0)) (PreH8 : (right0 >= 0)) (PreH9 : ((grant_rights (oldright) (right0)) >= 0)) (PreH10 : (class0 >= 0)) (PreH11 : (1 >= 0)) (PreH12 : (class0 <= 16)) (PreH13 : (dest0 < 64)) (PreH14 : (dp <> 0)) (PreH15 : (retval = 0)) (PreH16 : (dest0 < 63)) (PreH17 : (0 <= q)) (PreH18 : (q < 64)) (PreH19 : (cp <> 0)) (PreH20 : (p <> 0)) (PreH21 : (run <> 0)) (PreH22 : ((Z.land auth 64) <> 0)) (PreH23 : (parent = q)) (PreH24 : (dest0 <> q)) (PreH25 : (class0 <= 16)) (PreH26 : (dp <> 0)) (PreH27 : (p <> dp)) ,
  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p <> dp) ” 
  &&  “ (0 = 0) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (dest0 * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |-> 1)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |-> class0)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (class0 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> (grant_rights (oldright) (right0)))
.

Definition grant_cspace_cap_return_wit_14 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (q: Z) (p: Z) (cp: Z) (PreH1 : (p = 0)) (PreH2 : (destTask_Prio_pre < 63)) (PreH3 : (0 <= destTask_Prio_pre)) (PreH4 : (destTask_Prio_pre <= 255)) (PreH5 : (cap_Right_pre <= UINT_MAX)) (PreH6 : (cap_Class_pre <= UINT_MAX)) (PreH7 : (cap_Right_pre >= 0)) (PreH8 : (cap_Class_pre >= 0)) (PreH9 : (destTask_Prio_pre = dest0)) (PreH10 : (cap_Class_pre = class0)) (PreH11 : (cap_Right_pre = right0)) (PreH12 : (destTask_Prio_pre < 63)) (PreH13 : (0 <= q)) (PreH14 : (q < 64)) (PreH15 : (cp <> 0)) (PreH16 : (p = 0)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p = 0) ” 
  &&  “ (11 = 11) ”
  &&  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
.

Definition grant_cspace_cap_return_wit_15 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (PreH1 : (destTask_Prio_pre >= 63)) (PreH2 : (0 <= destTask_Prio_pre)) (PreH3 : (destTask_Prio_pre <= 255)) (PreH4 : (cap_Right_pre <= UINT_MAX)) (PreH5 : (cap_Class_pre <= UINT_MAX)) (PreH6 : (cap_Right_pre >= 0)) (PreH7 : (cap_Class_pre >= 0)) (PreH8 : (destTask_Prio_pre = dest0)) (PreH9 : (cap_Class_pre = class0)) (PreH10 : (cap_Right_pre = right0)) (PreH11 : (destTask_Prio_pre >= 63)) ,
  TT && emp 
|--
  “ (dest0 >= 63) ” 
  &&  “ (42 = 42) ”
  &&  emp
.

Definition grant_cspace_cap_partial_solve_wit_1 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre = q)) (PreH27 : (dp = p)) (PreH28 : (cap_Class_pre <= 16)) (PreH29 : (dp <> 0)) (PreH30 : (p = dp)) (PreH31 : (cap_Class_pre = 11)) (PreH32 : (oldright = auth)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (run <> 0) ” 
  &&  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
.

Definition grant_cspace_cap_partial_solve_wit_2 := 
forall (cap_Right_pre: Z) (cap_Class_pre: Z) (destTask_Prio_pre: Z) (right0: Z) (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (run <> 0)) (PreH2 : ((unsigned_last_nbits (run) (32)) = run)) (PreH3 : (0 <= run)) (PreH4 : (run <= 255)) (PreH5 : (p <> 0)) (PreH6 : (destTask_Prio_pre < 63)) (PreH7 : (0 <= destTask_Prio_pre)) (PreH8 : (destTask_Prio_pre <= 255)) (PreH9 : (oldright <= UINT_MAX)) (PreH10 : (cap_Right_pre <= UINT_MAX)) (PreH11 : (cap_Class_pre <= UINT_MAX)) (PreH12 : (oldright >= 0)) (PreH13 : (cap_Right_pre >= 0)) (PreH14 : (cap_Class_pre >= 0)) (PreH15 : (destTask_Prio_pre = dest0)) (PreH16 : (cap_Class_pre = class0)) (PreH17 : (cap_Right_pre = right0)) (PreH18 : (destTask_Prio_pre < 63)) (PreH19 : (0 <= q)) (PreH20 : (q < 64)) (PreH21 : (cp <> 0)) (PreH22 : (p <> 0)) (PreH23 : (run <> 0)) (PreH24 : ((Z.land auth 64) <> 0)) (PreH25 : (parent = q)) (PreH26 : (destTask_Prio_pre <> q)) (PreH27 : (cap_Class_pre <= 16)) (PreH28 : (dp <> 0)) (PreH29 : (p = dp)) (PreH30 : (cap_Class_pre = 11)) (PreH31 : (oldright = auth)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> oldright)
|--
  “ (run <> 0) ” 
  &&  “ ((unsigned_last_nbits (run) (32)) = run) ” 
  &&  “ (0 <= run) ” 
  &&  “ (run <= 255) ” 
  &&  “ (p <> 0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= destTask_Prio_pre) ” 
  &&  “ (destTask_Prio_pre <= 255) ” 
  &&  “ (oldright <= UINT_MAX) ” 
  &&  “ (cap_Right_pre <= UINT_MAX) ” 
  &&  “ (cap_Class_pre <= UINT_MAX) ” 
  &&  “ (oldright >= 0) ” 
  &&  “ (cap_Right_pre >= 0) ” 
  &&  “ (cap_Class_pre >= 0) ” 
  &&  “ (destTask_Prio_pre = dest0) ” 
  &&  “ (cap_Class_pre = class0) ” 
  &&  “ (cap_Right_pre = right0) ” 
  &&  “ (destTask_Prio_pre < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (destTask_Prio_pre <> q) ” 
  &&  “ (cap_Class_pre <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (cap_Class_pre = 11) ” 
  &&  “ (oldright = auth) ”
  &&  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (destTask_Prio_pre * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (destTask_Prio_pre * sizeof(PTR)))) # Ptr  |-> dp)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_type")) # UInt  |->_)
  **  ((&(((&((dp)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (cap_Class_pre * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_content")) # UInt  |->_)
.

Definition grant_cspace_cap_partial_solve_wit_3 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run = 0)) (PreH7 : (class0 > 16)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (class0 > 16) ”
  &&  (grant_call_pre dest0 class0 dp oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_partial_solve_wit_4 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run = 0)) (PreH7 : (dest0 = q)) (PreH8 : (dp = p)) (PreH9 : (class0 <= 16)) (PreH10 : (dp <> 0)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  (grant_call_pre dest0 class0 p oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_partial_solve_wit_5 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run = 0)) (PreH7 : (dest0 <> q)) (PreH8 : (class0 <= 16)) (PreH9 : (dp = 0)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp = 0) ”
  &&  (grant_call_pre dest0 class0 0 oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_partial_solve_wit_6 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run = 0)) (PreH7 : (dest0 <> q)) (PreH8 : (class0 <= 16)) (PreH9 : (dp <> 0)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run = 0) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ”
  &&  (grant_call_pre dest0 class0 dp oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
.

Definition grant_cspace_cap_partial_solve_wit_7 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run <> 0)) (PreH7 : ((Z.land auth 64) <> 0)) (PreH8 : (parent = q)) (PreH9 : (class0 > 16)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (class0 > 16) ”
  &&  (grant_call_pre dest0 class0 dp oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_partial_solve_wit_8 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run <> 0)) (PreH7 : ((Z.land auth 64) <> 0)) (PreH8 : (parent = q)) (PreH9 : (dest0 = q)) (PreH10 : (dp = p)) (PreH11 : (class0 <= 16)) (PreH12 : (dp <> 0)) (PreH13 : (p = dp)) (PreH14 : (class0 = 11)) (PreH15 : (oldright = auth)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 = 11) ” 
  &&  “ (oldright = auth) ”
  &&  (grant_call_pre dest0 class0 dp auth )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_partial_solve_wit_9 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run <> 0)) (PreH7 : ((Z.land auth 64) <> 0)) (PreH8 : (parent = q)) (PreH9 : (dest0 = q)) (PreH10 : (dp = p)) (PreH11 : (class0 <= 16)) (PreH12 : (dp <> 0)) (PreH13 : (p = dp)) (PreH14 : (class0 <> 11)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 = q) ” 
  &&  “ (dp = p) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 <> 11) ”
  &&  (grant_call_pre dest0 class0 dp oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_partial_solve_wit_10 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run <> 0)) (PreH7 : ((Z.land auth 64) <> 0)) (PreH8 : (parent = q)) (PreH9 : (dest0 <> q)) (PreH10 : (class0 <= 16)) (PreH11 : (dp = 0)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp = 0) ”
  &&  (grant_call_pre dest0 class0 0 oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_partial_solve_wit_11 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run <> 0)) (PreH7 : ((Z.land auth 64) <> 0)) (PreH8 : (parent = q)) (PreH9 : (dest0 <> q)) (PreH10 : (class0 <= 16)) (PreH11 : (dp <> 0)) (PreH12 : (p = dp)) (PreH13 : (class0 = 11)) (PreH14 : (oldright = auth)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 = 11) ” 
  &&  “ (oldright = auth) ”
  &&  (grant_call_pre dest0 class0 dp auth )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
.

Definition grant_cspace_cap_partial_solve_wit_12 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run <> 0)) (PreH7 : ((Z.land auth 64) <> 0)) (PreH8 : (parent = q)) (PreH9 : (dest0 <> q)) (PreH10 : (class0 <= 16)) (PreH11 : (dp <> 0)) (PreH12 : (p = dp)) (PreH13 : (class0 <> 11)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p = dp) ” 
  &&  “ (class0 <> 11) ”
  &&  (grant_call_pre dest0 class0 dp oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
.

Definition grant_cspace_cap_partial_solve_wit_13 := 
forall (class0: Z) (dest0: Z) (oldright: Z) (parent: Z) (auth: Z) (run: Z) (q: Z) (dp: Z) (p: Z) (cp: Z) (PreH1 : (dest0 < 63)) (PreH2 : (0 <= q)) (PreH3 : (q < 64)) (PreH4 : (cp <> 0)) (PreH5 : (p <> 0)) (PreH6 : (run <> 0)) (PreH7 : ((Z.land auth 64) <> 0)) (PreH8 : (parent = q)) (PreH9 : (dest0 <> q)) (PreH10 : (class0 <= 16)) (PreH11 : (dp <> 0)) (PreH12 : (p <> dp)) ,
  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
  **  (grant_call_pre dest0 class0 dp oldright )
|--
  “ (dest0 < 63) ” 
  &&  “ (0 <= q) ” 
  &&  “ (q < 64) ” 
  &&  “ (cp <> 0) ” 
  &&  “ (p <> 0) ” 
  &&  “ (run <> 0) ” 
  &&  “ ((Z.land auth 64) <> 0) ” 
  &&  “ (parent = q) ” 
  &&  “ (dest0 <> q) ” 
  &&  “ (class0 <= 16) ” 
  &&  “ (dp <> 0) ” 
  &&  “ (p <> dp) ”
  &&  (grant_call_pre dest0 class0 dp oldright )
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> q)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> cp)
  **  ((&((cp)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> q)
  **  (((( &( "OSCSpacePrioTbl" ) ) + (q * sizeof(PTR)))) # Ptr  |-> p)
  **  ((( &( "OSRunning" ) )) # UChar  |-> run)
  **  (((( &( "CapParent" ) ) + (dest0 * sizeof(UCHAR)))) # UChar  |-> parent)
  **  ((&(((&((p)  # "cspace" ->ₛ "cnode" .ₛ "slots") + (11 * sizeof( "slot" ))))  # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "category" .ₛ "category_right")) # UInt  |-> auth)
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
Axiom proof_of_ucos_Grant_Cap_safety_wit_20 : ucos_Grant_Cap_safety_wit_20.
Axiom proof_of_ucos_Grant_Cap_entail_wit_1 : ucos_Grant_Cap_entail_wit_1.
Axiom proof_of_ucos_Grant_Cap_entail_wit_2 : ucos_Grant_Cap_entail_wit_2.
Axiom proof_of_ucos_Grant_Cap_return_wit_1 : ucos_Grant_Cap_return_wit_1.
Axiom proof_of_ucos_Grant_Cap_return_wit_2 : ucos_Grant_Cap_return_wit_2.
Axiom proof_of_ucos_Grant_Cap_return_wit_3 : ucos_Grant_Cap_return_wit_3.
Axiom proof_of_ucos_Grant_Cap_return_wit_4 : ucos_Grant_Cap_return_wit_4.
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
Axiom proof_of_grant_cspace_cap_safety_wit_14 : grant_cspace_cap_safety_wit_14.
Axiom proof_of_grant_cspace_cap_safety_wit_15 : grant_cspace_cap_safety_wit_15.
Axiom proof_of_grant_cspace_cap_safety_wit_16 : grant_cspace_cap_safety_wit_16.
Axiom proof_of_grant_cspace_cap_safety_wit_17 : grant_cspace_cap_safety_wit_17.
Axiom proof_of_grant_cspace_cap_safety_wit_18 : grant_cspace_cap_safety_wit_18.
Axiom proof_of_grant_cspace_cap_safety_wit_19 : grant_cspace_cap_safety_wit_19.
Axiom proof_of_grant_cspace_cap_safety_wit_20 : grant_cspace_cap_safety_wit_20.
Axiom proof_of_grant_cspace_cap_safety_wit_21 : grant_cspace_cap_safety_wit_21.
Axiom proof_of_grant_cspace_cap_safety_wit_22 : grant_cspace_cap_safety_wit_22.
Axiom proof_of_grant_cspace_cap_safety_wit_23 : grant_cspace_cap_safety_wit_23.
Axiom proof_of_grant_cspace_cap_safety_wit_24 : grant_cspace_cap_safety_wit_24.
Axiom proof_of_grant_cspace_cap_safety_wit_25 : grant_cspace_cap_safety_wit_25.
Axiom proof_of_grant_cspace_cap_safety_wit_26 : grant_cspace_cap_safety_wit_26.
Axiom proof_of_grant_cspace_cap_safety_wit_27 : grant_cspace_cap_safety_wit_27.
Axiom proof_of_grant_cspace_cap_safety_wit_28 : grant_cspace_cap_safety_wit_28.
Axiom proof_of_grant_cspace_cap_safety_wit_29 : grant_cspace_cap_safety_wit_29.
Axiom proof_of_grant_cspace_cap_safety_wit_30 : grant_cspace_cap_safety_wit_30.
Axiom proof_of_grant_cspace_cap_safety_wit_31 : grant_cspace_cap_safety_wit_31.
Axiom proof_of_grant_cspace_cap_safety_wit_32 : grant_cspace_cap_safety_wit_32.
Axiom proof_of_grant_cspace_cap_safety_wit_33 : grant_cspace_cap_safety_wit_33.
Axiom proof_of_grant_cspace_cap_safety_wit_34 : grant_cspace_cap_safety_wit_34.
Axiom proof_of_grant_cspace_cap_safety_wit_35 : grant_cspace_cap_safety_wit_35.
Axiom proof_of_grant_cspace_cap_safety_wit_36 : grant_cspace_cap_safety_wit_36.
Axiom proof_of_grant_cspace_cap_safety_wit_37 : grant_cspace_cap_safety_wit_37.
Axiom proof_of_grant_cspace_cap_safety_wit_38 : grant_cspace_cap_safety_wit_38.
Axiom proof_of_grant_cspace_cap_safety_wit_39 : grant_cspace_cap_safety_wit_39.
Axiom proof_of_grant_cspace_cap_safety_wit_40 : grant_cspace_cap_safety_wit_40.
Axiom proof_of_grant_cspace_cap_safety_wit_41 : grant_cspace_cap_safety_wit_41.
Axiom proof_of_grant_cspace_cap_safety_wit_42 : grant_cspace_cap_safety_wit_42.
Axiom proof_of_grant_cspace_cap_safety_wit_43 : grant_cspace_cap_safety_wit_43.
Axiom proof_of_grant_cspace_cap_safety_wit_44 : grant_cspace_cap_safety_wit_44.
Axiom proof_of_grant_cspace_cap_safety_wit_45 : grant_cspace_cap_safety_wit_45.
Axiom proof_of_grant_cspace_cap_safety_wit_46 : grant_cspace_cap_safety_wit_46.
Axiom proof_of_grant_cspace_cap_safety_wit_47 : grant_cspace_cap_safety_wit_47.
Axiom proof_of_grant_cspace_cap_safety_wit_48 : grant_cspace_cap_safety_wit_48.
Axiom proof_of_grant_cspace_cap_safety_wit_49 : grant_cspace_cap_safety_wit_49.
Axiom proof_of_grant_cspace_cap_safety_wit_50 : grant_cspace_cap_safety_wit_50.
Axiom proof_of_grant_cspace_cap_safety_wit_51 : grant_cspace_cap_safety_wit_51.
Axiom proof_of_grant_cspace_cap_safety_wit_52 : grant_cspace_cap_safety_wit_52.
Axiom proof_of_grant_cspace_cap_safety_wit_53 : grant_cspace_cap_safety_wit_53.
Axiom proof_of_grant_cspace_cap_safety_wit_54 : grant_cspace_cap_safety_wit_54.
Axiom proof_of_grant_cspace_cap_safety_wit_55 : grant_cspace_cap_safety_wit_55.
Axiom proof_of_grant_cspace_cap_safety_wit_56 : grant_cspace_cap_safety_wit_56.
Axiom proof_of_grant_cspace_cap_safety_wit_57 : grant_cspace_cap_safety_wit_57.
Axiom proof_of_grant_cspace_cap_safety_wit_58 : grant_cspace_cap_safety_wit_58.
Axiom proof_of_grant_cspace_cap_safety_wit_59 : grant_cspace_cap_safety_wit_59.
Axiom proof_of_grant_cspace_cap_safety_wit_60 : grant_cspace_cap_safety_wit_60.
Axiom proof_of_grant_cspace_cap_safety_wit_61 : grant_cspace_cap_safety_wit_61.
Axiom proof_of_grant_cspace_cap_safety_wit_62 : grant_cspace_cap_safety_wit_62.
Axiom proof_of_grant_cspace_cap_safety_wit_63 : grant_cspace_cap_safety_wit_63.
Axiom proof_of_grant_cspace_cap_safety_wit_64 : grant_cspace_cap_safety_wit_64.
Axiom proof_of_grant_cspace_cap_safety_wit_65 : grant_cspace_cap_safety_wit_65.
Axiom proof_of_grant_cspace_cap_safety_wit_66 : grant_cspace_cap_safety_wit_66.
Axiom proof_of_grant_cspace_cap_safety_wit_67 : grant_cspace_cap_safety_wit_67.
Axiom proof_of_grant_cspace_cap_safety_wit_68 : grant_cspace_cap_safety_wit_68.
Axiom proof_of_grant_cspace_cap_safety_wit_69 : grant_cspace_cap_safety_wit_69.
Axiom proof_of_grant_cspace_cap_safety_wit_70 : grant_cspace_cap_safety_wit_70.
Axiom proof_of_grant_cspace_cap_safety_wit_71 : grant_cspace_cap_safety_wit_71.
Axiom proof_of_grant_cspace_cap_safety_wit_72 : grant_cspace_cap_safety_wit_72.
Axiom proof_of_grant_cspace_cap_safety_wit_73 : grant_cspace_cap_safety_wit_73.
Axiom proof_of_grant_cspace_cap_safety_wit_74 : grant_cspace_cap_safety_wit_74.
Axiom proof_of_grant_cspace_cap_safety_wit_75 : grant_cspace_cap_safety_wit_75.
Axiom proof_of_grant_cspace_cap_safety_wit_76 : grant_cspace_cap_safety_wit_76.
Axiom proof_of_grant_cspace_cap_safety_wit_77 : grant_cspace_cap_safety_wit_77.
Axiom proof_of_grant_cspace_cap_safety_wit_78 : grant_cspace_cap_safety_wit_78.
Axiom proof_of_grant_cspace_cap_safety_wit_79 : grant_cspace_cap_safety_wit_79.
Axiom proof_of_grant_cspace_cap_safety_wit_80 : grant_cspace_cap_safety_wit_80.
Axiom proof_of_grant_cspace_cap_safety_wit_81 : grant_cspace_cap_safety_wit_81.
Axiom proof_of_grant_cspace_cap_safety_wit_82 : grant_cspace_cap_safety_wit_82.
Axiom proof_of_grant_cspace_cap_safety_wit_83 : grant_cspace_cap_safety_wit_83.
Axiom proof_of_grant_cspace_cap_safety_wit_84 : grant_cspace_cap_safety_wit_84.
Axiom proof_of_grant_cspace_cap_safety_wit_85 : grant_cspace_cap_safety_wit_85.
Axiom proof_of_grant_cspace_cap_safety_wit_86 : grant_cspace_cap_safety_wit_86.
Axiom proof_of_grant_cspace_cap_safety_wit_87 : grant_cspace_cap_safety_wit_87.
Axiom proof_of_grant_cspace_cap_safety_wit_88 : grant_cspace_cap_safety_wit_88.
Axiom proof_of_grant_cspace_cap_safety_wit_89 : grant_cspace_cap_safety_wit_89.
Axiom proof_of_grant_cspace_cap_safety_wit_90 : grant_cspace_cap_safety_wit_90.
Axiom proof_of_grant_cspace_cap_safety_wit_91 : grant_cspace_cap_safety_wit_91.
Axiom proof_of_grant_cspace_cap_safety_wit_92 : grant_cspace_cap_safety_wit_92.
Axiom proof_of_grant_cspace_cap_safety_wit_93 : grant_cspace_cap_safety_wit_93.
Axiom proof_of_grant_cspace_cap_safety_wit_94 : grant_cspace_cap_safety_wit_94.
Axiom proof_of_grant_cspace_cap_safety_wit_95 : grant_cspace_cap_safety_wit_95.
Axiom proof_of_grant_cspace_cap_safety_wit_96 : grant_cspace_cap_safety_wit_96.
Axiom proof_of_grant_cspace_cap_safety_wit_97 : grant_cspace_cap_safety_wit_97.
Axiom proof_of_grant_cspace_cap_safety_wit_98 : grant_cspace_cap_safety_wit_98.
Axiom proof_of_grant_cspace_cap_safety_wit_99 : grant_cspace_cap_safety_wit_99.
Axiom proof_of_grant_cspace_cap_safety_wit_100 : grant_cspace_cap_safety_wit_100.
Axiom proof_of_grant_cspace_cap_safety_wit_101 : grant_cspace_cap_safety_wit_101.
Axiom proof_of_grant_cspace_cap_safety_wit_102 : grant_cspace_cap_safety_wit_102.
Axiom proof_of_grant_cspace_cap_safety_wit_103 : grant_cspace_cap_safety_wit_103.
Axiom proof_of_grant_cspace_cap_safety_wit_104 : grant_cspace_cap_safety_wit_104.
Axiom proof_of_grant_cspace_cap_safety_wit_105 : grant_cspace_cap_safety_wit_105.
Axiom proof_of_grant_cspace_cap_safety_wit_106 : grant_cspace_cap_safety_wit_106.
Axiom proof_of_grant_cspace_cap_safety_wit_107 : grant_cspace_cap_safety_wit_107.
Axiom proof_of_grant_cspace_cap_safety_wit_108 : grant_cspace_cap_safety_wit_108.
Axiom proof_of_grant_cspace_cap_safety_wit_109 : grant_cspace_cap_safety_wit_109.
Axiom proof_of_grant_cspace_cap_safety_wit_110 : grant_cspace_cap_safety_wit_110.
Axiom proof_of_grant_cspace_cap_safety_wit_111 : grant_cspace_cap_safety_wit_111.
Axiom proof_of_grant_cspace_cap_safety_wit_112 : grant_cspace_cap_safety_wit_112.
Axiom proof_of_grant_cspace_cap_safety_wit_113 : grant_cspace_cap_safety_wit_113.
Axiom proof_of_grant_cspace_cap_safety_wit_114 : grant_cspace_cap_safety_wit_114.
Axiom proof_of_grant_cspace_cap_safety_wit_115 : grant_cspace_cap_safety_wit_115.
Axiom proof_of_grant_cspace_cap_safety_wit_116 : grant_cspace_cap_safety_wit_116.
Axiom proof_of_grant_cspace_cap_safety_wit_117 : grant_cspace_cap_safety_wit_117.
Axiom proof_of_grant_cspace_cap_safety_wit_118 : grant_cspace_cap_safety_wit_118.
Axiom proof_of_grant_cspace_cap_safety_wit_119 : grant_cspace_cap_safety_wit_119.
Axiom proof_of_grant_cspace_cap_safety_wit_120 : grant_cspace_cap_safety_wit_120.
Axiom proof_of_grant_cspace_cap_safety_wit_121 : grant_cspace_cap_safety_wit_121.
Axiom proof_of_grant_cspace_cap_safety_wit_122 : grant_cspace_cap_safety_wit_122.
Axiom proof_of_grant_cspace_cap_safety_wit_123 : grant_cspace_cap_safety_wit_123.
Axiom proof_of_grant_cspace_cap_safety_wit_124 : grant_cspace_cap_safety_wit_124.
Axiom proof_of_grant_cspace_cap_safety_wit_125 : grant_cspace_cap_safety_wit_125.
Axiom proof_of_grant_cspace_cap_safety_wit_126 : grant_cspace_cap_safety_wit_126.
Axiom proof_of_grant_cspace_cap_entail_wit_1_1 : grant_cspace_cap_entail_wit_1_1.
Axiom proof_of_grant_cspace_cap_entail_wit_1_2 : grant_cspace_cap_entail_wit_1_2.
Axiom proof_of_grant_cspace_cap_entail_wit_1_3 : grant_cspace_cap_entail_wit_1_3.
Axiom proof_of_grant_cspace_cap_entail_wit_1_4 : grant_cspace_cap_entail_wit_1_4.
Axiom proof_of_grant_cspace_cap_entail_wit_1_5 : grant_cspace_cap_entail_wit_1_5.
Axiom proof_of_grant_cspace_cap_entail_wit_1_6 : grant_cspace_cap_entail_wit_1_6.
Axiom proof_of_grant_cspace_cap_entail_wit_1_7 : grant_cspace_cap_entail_wit_1_7.
Axiom proof_of_grant_cspace_cap_entail_wit_1_8 : grant_cspace_cap_entail_wit_1_8.
Axiom proof_of_grant_cspace_cap_entail_wit_1_9 : grant_cspace_cap_entail_wit_1_9.
Axiom proof_of_grant_cspace_cap_entail_wit_1_10 : grant_cspace_cap_entail_wit_1_10.
Axiom proof_of_grant_cspace_cap_entail_wit_1_11 : grant_cspace_cap_entail_wit_1_11.
Axiom proof_of_grant_cspace_cap_entail_wit_1_12 : grant_cspace_cap_entail_wit_1_12.
Axiom proof_of_grant_cspace_cap_entail_wit_1_13 : grant_cspace_cap_entail_wit_1_13.
Axiom proof_of_grant_cspace_cap_entail_wit_1_14 : grant_cspace_cap_entail_wit_1_14.
Axiom proof_of_grant_cspace_cap_entail_wit_1_15 : grant_cspace_cap_entail_wit_1_15.
Axiom proof_of_grant_cspace_cap_entail_wit_2_1 : grant_cspace_cap_entail_wit_2_1.
Axiom proof_of_grant_cspace_cap_entail_wit_2_2 : grant_cspace_cap_entail_wit_2_2.
Axiom proof_of_grant_cspace_cap_entail_wit_2_3 : grant_cspace_cap_entail_wit_2_3.
Axiom proof_of_grant_cspace_cap_entail_wit_2_4 : grant_cspace_cap_entail_wit_2_4.
Axiom proof_of_grant_cspace_cap_entail_wit_2_5 : grant_cspace_cap_entail_wit_2_5.
Axiom proof_of_grant_cspace_cap_entail_wit_2_6 : grant_cspace_cap_entail_wit_2_6.
Axiom proof_of_grant_cspace_cap_entail_wit_2_7 : grant_cspace_cap_entail_wit_2_7.
Axiom proof_of_grant_cspace_cap_entail_wit_2_8 : grant_cspace_cap_entail_wit_2_8.
Axiom proof_of_grant_cspace_cap_entail_wit_2_9 : grant_cspace_cap_entail_wit_2_9.
Axiom proof_of_grant_cspace_cap_entail_wit_2_10 : grant_cspace_cap_entail_wit_2_10.
Axiom proof_of_grant_cspace_cap_entail_wit_2_11 : grant_cspace_cap_entail_wit_2_11.
Axiom proof_of_grant_cspace_cap_entail_wit_2_12 : grant_cspace_cap_entail_wit_2_12.
Axiom proof_of_grant_cspace_cap_entail_wit_2_13 : grant_cspace_cap_entail_wit_2_13.
Axiom proof_of_grant_cspace_cap_entail_wit_2_14 : grant_cspace_cap_entail_wit_2_14.
Axiom proof_of_grant_cspace_cap_entail_wit_2_15 : grant_cspace_cap_entail_wit_2_15.
Axiom proof_of_grant_cspace_cap_entail_wit_3_1 : grant_cspace_cap_entail_wit_3_1.
Axiom proof_of_grant_cspace_cap_entail_wit_3_2 : grant_cspace_cap_entail_wit_3_2.
Axiom proof_of_grant_cspace_cap_entail_wit_3_3 : grant_cspace_cap_entail_wit_3_3.
Axiom proof_of_grant_cspace_cap_entail_wit_3_4 : grant_cspace_cap_entail_wit_3_4.
Axiom proof_of_grant_cspace_cap_entail_wit_3_5 : grant_cspace_cap_entail_wit_3_5.
Axiom proof_of_grant_cspace_cap_entail_wit_3_6 : grant_cspace_cap_entail_wit_3_6.
Axiom proof_of_grant_cspace_cap_entail_wit_3_7 : grant_cspace_cap_entail_wit_3_7.
Axiom proof_of_grant_cspace_cap_entail_wit_3_8 : grant_cspace_cap_entail_wit_3_8.
Axiom proof_of_grant_cspace_cap_entail_wit_3_9 : grant_cspace_cap_entail_wit_3_9.
Axiom proof_of_grant_cspace_cap_entail_wit_3_10 : grant_cspace_cap_entail_wit_3_10.
Axiom proof_of_grant_cspace_cap_entail_wit_3_11 : grant_cspace_cap_entail_wit_3_11.
Axiom proof_of_grant_cspace_cap_entail_wit_3_12 : grant_cspace_cap_entail_wit_3_12.
Axiom proof_of_grant_cspace_cap_entail_wit_3_13 : grant_cspace_cap_entail_wit_3_13.
Axiom proof_of_grant_cspace_cap_entail_wit_4_1 : grant_cspace_cap_entail_wit_4_1.
Axiom proof_of_grant_cspace_cap_entail_wit_4_2 : grant_cspace_cap_entail_wit_4_2.
Axiom proof_of_grant_cspace_cap_entail_wit_4_3 : grant_cspace_cap_entail_wit_4_3.
Axiom proof_of_grant_cspace_cap_entail_wit_4_4 : grant_cspace_cap_entail_wit_4_4.
Axiom proof_of_grant_cspace_cap_entail_wit_4_5 : grant_cspace_cap_entail_wit_4_5.
Axiom proof_of_grant_cspace_cap_entail_wit_4_6 : grant_cspace_cap_entail_wit_4_6.
Axiom proof_of_grant_cspace_cap_entail_wit_4_7 : grant_cspace_cap_entail_wit_4_7.
Axiom proof_of_grant_cspace_cap_entail_wit_4_8 : grant_cspace_cap_entail_wit_4_8.
Axiom proof_of_grant_cspace_cap_entail_wit_4_9 : grant_cspace_cap_entail_wit_4_9.
Axiom proof_of_grant_cspace_cap_entail_wit_4_10 : grant_cspace_cap_entail_wit_4_10.
Axiom proof_of_grant_cspace_cap_entail_wit_4_11 : grant_cspace_cap_entail_wit_4_11.
Axiom proof_of_grant_cspace_cap_entail_wit_4_12 : grant_cspace_cap_entail_wit_4_12.
Axiom proof_of_grant_cspace_cap_entail_wit_4_13 : grant_cspace_cap_entail_wit_4_13.
Axiom proof_of_grant_cspace_cap_entail_wit_5_1 : grant_cspace_cap_entail_wit_5_1.
Axiom proof_of_grant_cspace_cap_entail_wit_5_2 : grant_cspace_cap_entail_wit_5_2.
Axiom proof_of_grant_cspace_cap_entail_wit_5_3 : grant_cspace_cap_entail_wit_5_3.
Axiom proof_of_grant_cspace_cap_entail_wit_5_4 : grant_cspace_cap_entail_wit_5_4.
Axiom proof_of_grant_cspace_cap_entail_wit_5_5 : grant_cspace_cap_entail_wit_5_5.
Axiom proof_of_grant_cspace_cap_entail_wit_5_6 : grant_cspace_cap_entail_wit_5_6.
Axiom proof_of_grant_cspace_cap_entail_wit_5_7 : grant_cspace_cap_entail_wit_5_7.
Axiom proof_of_grant_cspace_cap_entail_wit_5_8 : grant_cspace_cap_entail_wit_5_8.
Axiom proof_of_grant_cspace_cap_entail_wit_5_9 : grant_cspace_cap_entail_wit_5_9.
Axiom proof_of_grant_cspace_cap_entail_wit_5_10 : grant_cspace_cap_entail_wit_5_10.
Axiom proof_of_grant_cspace_cap_entail_wit_5_11 : grant_cspace_cap_entail_wit_5_11.
Axiom proof_of_grant_cspace_cap_entail_wit_6_1 : grant_cspace_cap_entail_wit_6_1.
Axiom proof_of_grant_cspace_cap_entail_wit_6_2 : grant_cspace_cap_entail_wit_6_2.
Axiom proof_of_grant_cspace_cap_entail_wit_6_3 : grant_cspace_cap_entail_wit_6_3.
Axiom proof_of_grant_cspace_cap_entail_wit_6_4 : grant_cspace_cap_entail_wit_6_4.
Axiom proof_of_grant_cspace_cap_entail_wit_6_5 : grant_cspace_cap_entail_wit_6_5.
Axiom proof_of_grant_cspace_cap_entail_wit_6_6 : grant_cspace_cap_entail_wit_6_6.
Axiom proof_of_grant_cspace_cap_entail_wit_6_7 : grant_cspace_cap_entail_wit_6_7.
Axiom proof_of_grant_cspace_cap_entail_wit_6_8 : grant_cspace_cap_entail_wit_6_8.
Axiom proof_of_grant_cspace_cap_entail_wit_6_9 : grant_cspace_cap_entail_wit_6_9.
Axiom proof_of_grant_cspace_cap_entail_wit_6_10 : grant_cspace_cap_entail_wit_6_10.
Axiom proof_of_grant_cspace_cap_entail_wit_6_11 : grant_cspace_cap_entail_wit_6_11.
Axiom proof_of_grant_cspace_cap_return_wit_1 : grant_cspace_cap_return_wit_1.
Axiom proof_of_grant_cspace_cap_return_wit_2 : grant_cspace_cap_return_wit_2.
Axiom proof_of_grant_cspace_cap_return_wit_3 : grant_cspace_cap_return_wit_3.
Axiom proof_of_grant_cspace_cap_return_wit_4 : grant_cspace_cap_return_wit_4.
Axiom proof_of_grant_cspace_cap_return_wit_5 : grant_cspace_cap_return_wit_5.
Axiom proof_of_grant_cspace_cap_return_wit_6 : grant_cspace_cap_return_wit_6.
Axiom proof_of_grant_cspace_cap_return_wit_7 : grant_cspace_cap_return_wit_7.
Axiom proof_of_grant_cspace_cap_return_wit_8 : grant_cspace_cap_return_wit_8.
Axiom proof_of_grant_cspace_cap_return_wit_9 : grant_cspace_cap_return_wit_9.
Axiom proof_of_grant_cspace_cap_return_wit_10 : grant_cspace_cap_return_wit_10.
Axiom proof_of_grant_cspace_cap_return_wit_11 : grant_cspace_cap_return_wit_11.
Axiom proof_of_grant_cspace_cap_return_wit_12 : grant_cspace_cap_return_wit_12.
Axiom proof_of_grant_cspace_cap_return_wit_13 : grant_cspace_cap_return_wit_13.
Axiom proof_of_grant_cspace_cap_return_wit_14 : grant_cspace_cap_return_wit_14.
Axiom proof_of_grant_cspace_cap_return_wit_15 : grant_cspace_cap_return_wit_15.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_1 : grant_cspace_cap_partial_solve_wit_1.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_2 : grant_cspace_cap_partial_solve_wit_2.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_3 : grant_cspace_cap_partial_solve_wit_3.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_4 : grant_cspace_cap_partial_solve_wit_4.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_5 : grant_cspace_cap_partial_solve_wit_5.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_6 : grant_cspace_cap_partial_solve_wit_6.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_7 : grant_cspace_cap_partial_solve_wit_7.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_8 : grant_cspace_cap_partial_solve_wit_8.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_9 : grant_cspace_cap_partial_solve_wit_9.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_10 : grant_cspace_cap_partial_solve_wit_10.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_11 : grant_cspace_cap_partial_solve_wit_11.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_12 : grant_cspace_cap_partial_solve_wit_12.
Axiom proof_of_grant_cspace_cap_partial_solve_wit_13 : grant_cspace_cap_partial_solve_wit_13.

End VC_Correct.
