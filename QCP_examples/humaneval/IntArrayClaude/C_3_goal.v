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

(*----- Function below_zero -----*)

Definition below_zero_safety_wit_1 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) ,
  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  (IntArray.full operations_pre operations_size_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition below_zero_safety_wit_2 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) ,
  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  (IntArray.full operations_pre operations_size_pre l )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition below_zero_safety_wit_3 := 
forall (operations_size_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| (i < operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations" ) )) # Ptr  |-> operations)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
|--
  [| ((num + (Znth i l 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (num + (Znth i l 0) )) |]
.

Definition below_zero_safety_wit_4 := 
forall (operations_size_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| (i < operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
  **  ((( &( "num" ) )) # Int  |-> (num + (Znth i l 0) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations" ) )) # Ptr  |-> operations)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition below_zero_safety_wit_5 := 
forall (operations_size_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| ((num + (Znth i l 0) ) < 0) |] 
  &&  [| (i < operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
  **  ((( &( "num" ) )) # Int  |-> (num + (Znth i l 0) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations" ) )) # Ptr  |-> operations)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition below_zero_safety_wit_6 := 
forall (operations_size_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| ((num + (Znth i l 0) ) >= 0) |] 
  &&  [| (i < operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
  **  ((( &( "num" ) )) # Int  |-> (num + (Znth i l 0) ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations" ) )) # Ptr  |-> operations)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition below_zero_safety_wit_7 := 
forall (operations_size_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| (i >= operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations" ) )) # Ptr  |-> operations)
  **  (IntArray.full operations operations_size_pre l )
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition below_zero_entail_wit_1 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) ,
  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations_pre operations_size_pre l )
|--
  [| (0 = (sum ((sublist (0) (0) (l))))) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations_pre operations_size_pre l )
.

Definition below_zero_entail_wit_2 := 
forall (operations_size_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| ((num + (Znth i l 0) ) >= 0) |] 
  &&  [| (i < operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
|--
  [| ((num + (Znth i l 0) ) = (sum ((sublist (0) ((i + 1 )) (l))))) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
.

Definition below_zero_return_wit_1 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| ((num + (Znth i l 0) ) < 0) |] 
  &&  [| (i < operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> (0 <= (sum ((sublist (0) ((k_3 + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
|--
  ([| (1 = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |]
  &&  (IntArray.full operations_pre operations_size_pre l ))
  ||
  (EX (k_2: Z) ,
  [| (1 <> 0) |] 
  &&  [| (0 <= k_2) |] 
  &&  [| (k_2 < operations_size_pre) |] 
  &&  [| ((sum ((sublist (0) ((k_2 + 1 )) (l)))) < 0) |]
  &&  (IntArray.full operations_pre operations_size_pre l ))
.

Definition below_zero_return_wit_2 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| (i >= operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> (0 <= (sum ((sublist (0) ((k_3 + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
|--
  ([| (0 = 0) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |]
  &&  (IntArray.full operations_pre operations_size_pre l ))
  ||
  (EX (k_2: Z) ,
  [| (0 <> 0) |] 
  &&  [| (0 <= k_2) |] 
  &&  [| (k_2 < operations_size_pre) |] 
  &&  [| ((sum ((sublist (0) ((k_2 + 1 )) (l)))) < 0) |]
  &&  (IntArray.full operations_pre operations_size_pre l ))
.

Definition below_zero_partial_solve_wit_1 := 
forall (operations_size_pre: Z) (l: (@list Z)) (operations: Z) (i: Z) (num: Z) ,
  [| (i < operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (IntArray.full operations operations_size_pre l )
|--
  [| (i < operations_size_pre) |] 
  &&  [| (num = (sum ((sublist (0) (i) (l))))) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= operations_size_pre) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) |] 
  &&  [| (0 <= operations_size_pre) |] 
  &&  [| (operations_size_pre < INT_MAX) |]
  &&  (((operations + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i operations i 0 operations_size_pre l )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_below_zero_safety_wit_1 : below_zero_safety_wit_1.
Axiom proof_of_below_zero_safety_wit_2 : below_zero_safety_wit_2.
Axiom proof_of_below_zero_safety_wit_3 : below_zero_safety_wit_3.
Axiom proof_of_below_zero_safety_wit_4 : below_zero_safety_wit_4.
Axiom proof_of_below_zero_safety_wit_5 : below_zero_safety_wit_5.
Axiom proof_of_below_zero_safety_wit_6 : below_zero_safety_wit_6.
Axiom proof_of_below_zero_safety_wit_7 : below_zero_safety_wit_7.
Axiom proof_of_below_zero_entail_wit_1 : below_zero_entail_wit_1.
Axiom proof_of_below_zero_entail_wit_2 : below_zero_entail_wit_2.
Axiom proof_of_below_zero_return_wit_1 : below_zero_return_wit_1.
Axiom proof_of_below_zero_return_wit_2 : below_zero_return_wit_2.
Axiom proof_of_below_zero_partial_solve_wit_1 : below_zero_partial_solve_wit_1.

End VC_Correct.
