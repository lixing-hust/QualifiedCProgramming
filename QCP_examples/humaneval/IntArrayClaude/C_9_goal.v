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

(*----- Function rolling_max -----*)

Definition rolling_max_safety_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (lv: (@list Z)) ,
  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full out_pre numbers_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rolling_max_safety_wit_2 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (lv: (@list Z)) ,
  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  ((( &( "max" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full out_pre numbers_size_pre )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition rolling_max_safety_wit_3 := 
forall (out_pre: Z) (numbers_size_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| ((Znth i lv 0) <= max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> max)
  **  (IntArray.undef_seg out_pre (i + 1 ) numbers_size_pre )
  **  (IntArray.full numbers numbers_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers)
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition rolling_max_safety_wit_4 := 
forall (out_pre: Z) (numbers_size_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| ((Znth i lv 0) > max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.undef_seg out_pre (i + 1 ) numbers_size_pre )
  **  (IntArray.full numbers numbers_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> (Znth i lv 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers)
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition rolling_max_entail_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (lv: (@list Z)) ,
  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full out_pre numbers_size_pre )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (0 = (running_max_val (0) ((sublist (0) (0) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 0 (rolling_max_f (0) ((sublist (0) (0) (lv)))) )
  **  (IntArray.undef_seg out_pre 0 numbers_size_pre )
.

Definition rolling_max_entail_wit_2_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| ((Znth i lv 0) > max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.undef_seg out_pre (i + 1 ) numbers_size_pre )
  **  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size_pre) |] 
  &&  [| ((Znth i lv 0) = (running_max_val (0) ((sublist (0) ((i + 1 )) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 (i + 1 ) (rolling_max_f (0) ((sublist (0) ((i + 1 )) (lv)))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) numbers_size_pre )
.

Definition rolling_max_entail_wit_2_2 := 
forall (out_pre: Z) (numbers_size_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| ((Znth i lv 0) <= max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |-> max)
  **  (IntArray.undef_seg out_pre (i + 1 ) numbers_size_pre )
  **  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) ((i + 1 )) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 (i + 1 ) (rolling_max_f (0) ((sublist (0) ((i + 1 )) (lv)))) )
  **  (IntArray.undef_seg out_pre (i + 1 ) numbers_size_pre )
.

Definition rolling_max_return_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| (i >= numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i numbers_size_pre )
|--
  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.full out_pre numbers_size_pre (rolling_max_f (0) (lv)) )
.

Definition rolling_max_partial_solve_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i numbers_size_pre )
|--
  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((numbers + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i numbers i 0 numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i numbers_size_pre )
.

Definition rolling_max_partial_solve_wit_2 := 
forall (out_pre: Z) (numbers_size_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| ((Znth i lv 0) > max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i numbers_size_pre )
|--
  [| ((Znth i lv 0) > max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((numbers + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i numbers i 0 numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i numbers_size_pre )
.

Definition rolling_max_partial_solve_wit_3 := 
forall (out_pre: Z) (numbers_size_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| ((Znth i lv 0) > max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i numbers_size_pre )
|--
  [| ((Znth i lv 0) > max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) numbers_size_pre )
  **  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
.

Definition rolling_max_partial_solve_wit_4 := 
forall (out_pre: Z) (numbers_size_pre: Z) (lv: (@list Z)) (numbers: Z) (max: Z) (i: Z) ,
  [| ((Znth i lv 0) <= max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out_pre i numbers_size_pre )
|--
  [| ((Znth i lv 0) <= max) |] 
  &&  [| (i < numbers_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= numbers_size_pre) |] 
  &&  [| (max = (running_max_val (0) ((sublist (0) (i) (lv))))) |] 
  &&  [| (0 <= numbers_size_pre) |] 
  &&  [| (numbers_size_pre < INT_MAX) |]
  &&  (((out_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre (i + 1 ) numbers_size_pre )
  **  (IntArray.full numbers numbers_size_pre lv )
  **  (IntArray.seg out_pre 0 i (rolling_max_f (0) ((sublist (0) (i) (lv)))) )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_rolling_max_safety_wit_1 : rolling_max_safety_wit_1.
Axiom proof_of_rolling_max_safety_wit_2 : rolling_max_safety_wit_2.
Axiom proof_of_rolling_max_safety_wit_3 : rolling_max_safety_wit_3.
Axiom proof_of_rolling_max_safety_wit_4 : rolling_max_safety_wit_4.
Axiom proof_of_rolling_max_entail_wit_1 : rolling_max_entail_wit_1.
Axiom proof_of_rolling_max_entail_wit_2_1 : rolling_max_entail_wit_2_1.
Axiom proof_of_rolling_max_entail_wit_2_2 : rolling_max_entail_wit_2_2.
Axiom proof_of_rolling_max_return_wit_1 : rolling_max_return_wit_1.
Axiom proof_of_rolling_max_partial_solve_wit_1 : rolling_max_partial_solve_wit_1.
Axiom proof_of_rolling_max_partial_solve_wit_2 : rolling_max_partial_solve_wit_2.
Axiom proof_of_rolling_max_partial_solve_wit_3 : rolling_max_partial_solve_wit_3.
Axiom proof_of_rolling_max_partial_solve_wit_4 : rolling_max_partial_solve_wit_4.

End VC_Correct.
