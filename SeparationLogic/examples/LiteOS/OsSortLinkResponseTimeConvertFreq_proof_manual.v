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
Require Import OsSortLinkResponseTimeConvertFreq_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.LiteOS.lib.sortlink.
Require Import SimpleC.EE.LiteOS.lib.dll.
Require Import SimpleC.EE.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec.
Proof. 
   pre_process.
   unfold store_swtmr_sorted_dll. 
   Intros y. subst y.
   Exists Z.
   Exists n (fun (p : addr) (swmtrID : SwtmrID) => [|p = &(((sg).(g_swtmrCBArray) # ("SWTMR_CTRL_S") + swmtrID % 5) ->ₛ "stSortList")|] && emp) l.
   entailer!.
   rewrite H0.
   unfold glob_vars_and_defs.SwtmrID.
   csimpl.
   entailer!.
   unfold SwtmrID.
   entailer!.
   rewrite <- derivable1_wand_sepcon_adjoint.
   Exists (&( "g_swtmrSortLink")).
   csimpl.
   entailer!.
Qed. 

Lemma proof_of_SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec.
Proof. 
   pre_process.
   unfold store_task_sorted_dll.
   Intros y. subst y.
   Exists Z.
   Exists n (fun (p : addr) (taskID : glob_vars_and_defs.TaskID) =>
    [|p = &( ((glob_vars_and_defs.g_taskCBArray sg) # "LosTaskCB" + taskID) ->ₛ "sortList")|] &&
    emp) l.
   entailer!.
   rewrite H0.
   unfold glob_vars_and_defs.TaskID.
   csimpl.
   entailer!.
   rewrite <- derivable1_wand_sepcon_adjoint.
   Exists (&( "g_taskSortLink")). 
   csimpl.
   entailer!.
Qed.