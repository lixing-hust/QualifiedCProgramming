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
Require Import coins_60.
Local Open Scope sac.
From SimpleC.EE Require Import common_strategy_goal.
From SimpleC.EE Require Import common_strategy_proof.

(*----- Function sum_to_n -----*)

Definition sum_to_n_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (problem_60_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (((n_pre * (n_pre + 1 ) ) <> (INT_MIN)) \/ (2 <> (-1))) |] 
  &&  [| (2 <> 0) |]
.

Definition sum_to_n_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (problem_60_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre * (n_pre + 1 ) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre * (n_pre + 1 ) )) |]
.

Definition sum_to_n_safety_wit_3 := 
forall (n_pre: Z) ,
  [| (problem_60_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| ((n_pre + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (n_pre + 1 )) |]
.

Definition sum_to_n_safety_wit_4 := 
forall (n_pre: Z) ,
  [| (problem_60_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sum_to_n_safety_wit_5 := 
forall (n_pre: Z) ,
  [| (problem_60_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (2 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 2) |]
.

Definition sum_to_n_return_wit_1 := 
forall (n_pre: Z) ,
  [| (problem_60_pre_z n_pre ) |] 
  &&  [| (1 <= n_pre) |] 
  &&  [| (n_pre <= 46340) |]
  &&  emp
|--
  [| (problem_60_spec_z n_pre ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_sum_to_n_safety_wit_1 : sum_to_n_safety_wit_1.
Axiom proof_of_sum_to_n_safety_wit_2 : sum_to_n_safety_wit_2.
Axiom proof_of_sum_to_n_safety_wit_3 : sum_to_n_safety_wit_3.
Axiom proof_of_sum_to_n_safety_wit_4 : sum_to_n_safety_wit_4.
Axiom proof_of_sum_to_n_safety_wit_5 : sum_to_n_safety_wit_5.
Axiom proof_of_sum_to_n_return_wit_1 : sum_to_n_return_wit_1.

End VC_Correct.
