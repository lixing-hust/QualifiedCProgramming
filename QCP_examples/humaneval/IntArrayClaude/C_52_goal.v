Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
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
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_52.
Local Open Scope sac.
From SimpleC.EE Require Import int_array_strategy_goal.
From SimpleC.EE Require Import int_array_strategy_proof.
From SimpleC.EE Require Import uint_array_strategy_goal.
From SimpleC.EE Require Import uint_array_strategy_proof.
From SimpleC.EE Require Import undef_uint_array_strategy_goal.
From SimpleC.EE Require Import undef_uint_array_strategy_proof.
From SimpleC.EE Require Import array_shape_strategy_goal.
From SimpleC.EE Require Import array_shape_strategy_proof.

(*----- Function below_threshold -----*)

Definition below_threshold_safety_wit_1 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (problem_52_pre input_l ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition below_threshold_safety_wit_2 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| ((Znth i input_l 0) >= t_pre) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition below_threshold_safety_wit_3 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition below_threshold_safety_wit_4 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| ((Znth i input_l 0) < t_pre) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition below_threshold_entail_wit_1 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |] 
  &&  [| (problem_52_pre input_l ) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition below_threshold_entail_wit_2 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| ((Znth i input_l 0) < t_pre) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition below_threshold_return_wit_1 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  ([| (1 = 0) |] 
  &&  [| (problem_52_spec input_l t_pre false ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
  ||
  ([| (1 <> 0) |] 
  &&  [| (problem_52_spec input_l t_pre true ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
.

Definition below_threshold_return_wit_2 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| ((Znth i input_l 0) >= t_pre) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  ([| (0 = 0) |] 
  &&  [| (problem_52_spec input_l t_pre false ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
  ||
  ([| (0 <> 0) |] 
  &&  [| (problem_52_spec input_l t_pre true ) |]
  &&  (IntArray.full l_pre l_size_pre input_l ))
.

Definition below_threshold_partial_solve_wit_1 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| (problem_52_pre input_l ) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (input_l) (0)) < t_pre)) |]
  &&  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_below_threshold_safety_wit_1 : below_threshold_safety_wit_1.
Axiom proof_of_below_threshold_safety_wit_2 : below_threshold_safety_wit_2.
Axiom proof_of_below_threshold_safety_wit_3 : below_threshold_safety_wit_3.
Axiom proof_of_below_threshold_safety_wit_4 : below_threshold_safety_wit_4.
Axiom proof_of_below_threshold_entail_wit_1 : below_threshold_entail_wit_1.
Axiom proof_of_below_threshold_entail_wit_2 : below_threshold_entail_wit_2.
Axiom proof_of_below_threshold_return_wit_1 : below_threshold_return_wit_1.
Axiom proof_of_below_threshold_return_wit_2 : below_threshold_return_wit_2.
Axiom proof_of_below_threshold_partial_solve_wit_1 : below_threshold_partial_solve_wit_1.

End VC_Correct.
