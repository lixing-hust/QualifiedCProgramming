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
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function car_race_collision -----*)

Definition car_race_collision_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre * n_pre ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre * n_pre )) |]
.

Definition car_race_collision_return_wit_1 := 
forall (n_pre: Z) ,
  [| (INT_MIN <= n_pre) |] 
  &&  [| (n_pre <= INT_MAX) |]
  &&  emp
|--
  [| ((n_pre * n_pre ) = (n_pre * n_pre )) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_car_race_collision_safety_wit_1 : car_race_collision_safety_wit_1.
Axiom proof_of_car_race_collision_return_wit_1 : car_race_collision_return_wit_1.

End VC_Correct.
