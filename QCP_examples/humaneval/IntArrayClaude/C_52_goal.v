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
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> t_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition below_threshold_safety_wit_2 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (t: Z) (i: Z) ,
  [| ((Znth i lv 0) >= t) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition below_threshold_safety_wit_3 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (t: Z) (i: Z) ,
  [| ((Znth i lv 0) < t) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition below_threshold_safety_wit_4 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (t: Z) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "l" ) )) # Ptr  |-> l)
  **  (IntArray.full l l_size_pre lv )
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition below_threshold_entail_wit_1 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) ,
  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l_pre l_size_pre lv )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (lv) (0)) < t_pre)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l_pre l_size_pre lv )
.

Definition below_threshold_entail_wit_2 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (t: Z) (i: Z) ,
  [| ((Znth i lv 0) < t) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= l_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
.

Definition below_threshold_return_wit_1 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) (l: Z) (t: Z) (i: Z) ,
  [| ((Znth i lv 0) >= t) |] 
  &&  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (k_3) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  (EX (k: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < l_size_pre) |] 
  &&  [| ((Znth (k) (lv) (0)) >= t_pre) |]
  &&  (IntArray.full l_pre l_size_pre lv ))
  ||
  ([| (0 <> 0) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < l_size_pre)) -> ((Znth (k_2) (lv) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre lv ))
.

Definition below_threshold_return_wit_2 := 
forall (t_pre: Z) (l_size_pre: Z) (l_pre: Z) (lv: (@list Z)) (l: Z) (t: Z) (i: Z) ,
  [| (i >= l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (k_3) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  (EX (k: Z) ,
  [| (1 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < l_size_pre) |] 
  &&  [| ((Znth (k) (lv) (0)) >= t_pre) |]
  &&  (IntArray.full l_pre l_size_pre lv ))
  ||
  ([| (1 <> 0) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < l_size_pre)) -> ((Znth (k_2) (lv) (0)) < t_pre)) |]
  &&  (IntArray.full l_pre l_size_pre lv ))
.

Definition below_threshold_partial_solve_wit_1 := 
forall (l_size_pre: Z) (lv: (@list Z)) (l: Z) (t: Z) (i: Z) ,
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (IntArray.full l l_size_pre lv )
|--
  [| (i < l_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= l_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) < t)) |] 
  &&  [| (0 <= l_size_pre) |] 
  &&  [| (l_size_pre < INT_MAX) |]
  &&  (((l + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i l i 0 l_size_pre lv )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
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
