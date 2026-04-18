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

(*----- Function sum_to_n -----*)

Definition sum_to_n_safety_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition sum_to_n_safety_wit_2 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  ((( &( "ret" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition sum_to_n_safety_wit_3 := 
forall (n_pre: Z) (ret: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (ret = (((i - 1 ) * i ) ÷ 2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> ret)
|--
  [| ((ret + i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (ret + i )) |]
.

Definition sum_to_n_safety_wit_4 := 
forall (n_pre: Z) (ret: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (ret = (((i - 1 ) * i ) ÷ 2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ret" ) )) # Int  |-> (ret + i ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition sum_to_n_entail_wit_1 := 
forall (n_pre: Z) ,
  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  emp
|--
  [| (1 <= 1) |] 
  &&  [| (1 <= (n_pre + 1 )) |] 
  &&  [| (0 = (((1 - 1 ) * 1 ) ÷ 2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  emp
.

Definition sum_to_n_entail_wit_2 := 
forall (n_pre: Z) (ret: Z) (i: Z) ,
  [| (i <= n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (ret = (((i - 1 ) * i ) ÷ 2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  emp
|--
  [| (1 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= (n_pre + 1 )) |] 
  &&  [| ((ret + i ) = ((((i + 1 ) - 1 ) * (i + 1 ) ) ÷ 2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  emp
.

Definition sum_to_n_entail_wit_3 := 
forall (n_pre: Z) (ret: Z) (i: Z) ,
  [| (i > n_pre) |] 
  &&  [| (1 <= i) |] 
  &&  [| (i <= (n_pre + 1 )) |] 
  &&  [| (ret = (((i - 1 ) * i ) ÷ 2 )) |] 
  &&  [| (0 <= n_pre) |] 
  &&  [| (INT_MIN <= ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |] 
  &&  [| (((n_pre * (n_pre + 1 ) ) ÷ 2 ) <= INT_MAX) |]
  &&  emp
|--
  [| (i = (n_pre + 1 )) |] 
  &&  [| (ret = ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |]
  &&  emp
.

Definition sum_to_n_return_wit_1 := 
forall (n_pre: Z) (i: Z) (ret: Z) ,
  [| (i = (n_pre + 1 )) |] 
  &&  [| (ret = ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |]
  &&  emp
|--
  [| (ret = ((n_pre * (n_pre + 1 ) ) ÷ 2 )) |]
  &&  emp
.

Module Type VC_Correct.

Include common_Strategy_Correct.

Axiom proof_of_sum_to_n_safety_wit_1 : sum_to_n_safety_wit_1.
Axiom proof_of_sum_to_n_safety_wit_2 : sum_to_n_safety_wit_2.
Axiom proof_of_sum_to_n_safety_wit_3 : sum_to_n_safety_wit_3.
Axiom proof_of_sum_to_n_safety_wit_4 : sum_to_n_safety_wit_4.
Axiom proof_of_sum_to_n_entail_wit_1 : sum_to_n_entail_wit_1.
Axiom proof_of_sum_to_n_entail_wit_2 : sum_to_n_entail_wit_2.
Axiom proof_of_sum_to_n_entail_wit_3 : sum_to_n_entail_wit_3.
Axiom proof_of_sum_to_n_return_wit_1 : sum_to_n_return_wit_1.

End VC_Correct.
