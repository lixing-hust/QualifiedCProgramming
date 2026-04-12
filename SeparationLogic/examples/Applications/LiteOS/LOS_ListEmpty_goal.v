Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications.LiteOS.lib.tick_backup.
Local Open Scope sac.
From SimpleC.EE.QCP_democases Require Import common_strategy_goal.
From SimpleC.EE.QCP_democases Require Import common_strategy_proof.
From SimpleC.EE.Applications Require Import los_sortlink_strategy_goal.
From SimpleC.EE.Applications Require Import los_sortlink_strategy_proof.

(*----- Function LOS_ListEmpty -----*)

Definition LOS_ListEmpty_return_wit_1 := 
forall (A: Type) (node_pre: Z) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (h: Z) (pt: Z) ,
  [| (h <> node_pre) |]
  &&  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg storeA h node_pre node_pre pt l )
|--
  ([| (l <> nil) |] 
  &&  [| (0 = 0) |]
  &&  (store_dll storeA node_pre l ))
  ||
  ([| (l = nil) |] 
  &&  [| (0 = 1) |]
  &&  (store_dll storeA node_pre l ))
.

Definition LOS_ListEmpty_return_wit_2 := 
forall (A: Type) (node_pre: Z) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (h: Z) (pt: Z) ,
  [| (h = node_pre) |]
  &&  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((&((node_pre)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg storeA h node_pre node_pre pt l )
|--
  ([| (l <> nil) |] 
  &&  [| (1 = 0) |]
  &&  (store_dll storeA node_pre l ))
  ||
  ([| (l = nil) |] 
  &&  [| (1 = 1) |]
  &&  (store_dll storeA node_pre l ))
.

Definition LOS_ListEmpty_partial_solve_wit_1 := 
forall (A: Type) (node_pre: Z) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) ,
  (store_dll storeA node_pre l )
|--
  (store_dll storeA node_pre l )
.

Definition LOS_ListEmpty_which_implies_wit_1 := 
forall (A: Type) (l: (@list (@DL_Node A))) (storeA: (Z -> (A -> Assertion))) (node: Z) ,
  (store_dll storeA node l )
|--
  EX (h: Z)  (pt: Z) ,
  ((&((node)  # "LOS_DL_LIST" ->ₛ "pstPrev")) # Ptr  |-> pt)
  **  ((&((node)  # "LOS_DL_LIST" ->ₛ "pstNext")) # Ptr  |-> h)
  **  (dllseg storeA h node node pt l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include los_sortlink_Strategy_Correct.

Axiom proof_of_LOS_ListEmpty_return_wit_1 : LOS_ListEmpty_return_wit_1.
Axiom proof_of_LOS_ListEmpty_return_wit_2 : LOS_ListEmpty_return_wit_2.
Axiom proof_of_LOS_ListEmpty_partial_solve_wit_1 : LOS_ListEmpty_partial_solve_wit_1.
Axiom proof_of_LOS_ListEmpty_which_implies_wit_1 : LOS_ListEmpty_which_implies_wit_1.

End VC_Correct.
