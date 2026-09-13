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
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_goal.
From SimpleC.EE.osverify_qcp.cases Require Import grant_cspace_cap_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Goal grant_cspace_cap_return_wit_11_callee_success.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply_p (store_uchar_range (&( "OSRunning" )) running).
  Intros_p Hrunning_range.
  replace Byte.max_unsigned with (2 ^ 8 - 1) in Hrunning_range by reflexivity.
  rewrite unsigned_last_nbits_eq in PreH3 by lia.
  subst running.
  Right.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
  Show.
Abort.
