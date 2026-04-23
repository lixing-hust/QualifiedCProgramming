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
Require Import coins_72.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function will_it_fly -----*)

Definition will_it_fly_safety_wit_1 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) ,
  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |]
  &&  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (IntArray.full q_pre q_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition will_it_fly_safety_wit_2 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) ,
  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |]
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  (IntArray.full q_pre q_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition will_it_fly_safety_wit_3 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (((q_size_pre - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((q_size_pre - 1 ) - i )) |]
.

Definition will_it_fly_safety_wit_4 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| ((q_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q_size_pre - 1 )) |]
.

Definition will_it_fly_safety_wit_5 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition will_it_fly_safety_wit_6 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition will_it_fly_safety_wit_7 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
|--
  [| ((s + (Znth i lv 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s + (Znth i lv 0) )) |]
.

Definition will_it_fly_safety_wit_8 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (Znth i lv 0) ))
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition will_it_fly_safety_wit_9 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (s > w_pre) |] 
  &&  [| (i >= q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full q_pre q_size_pre lv )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition will_it_fly_safety_wit_10 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (s <= w_pre) |] 
  &&  [| (i >= q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  (IntArray.full q_pre q_size_pre lv )
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition will_it_fly_entail_wit_1 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) ,
  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= 0) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (0 = (sum ((sublist (0) (0) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
.

Definition will_it_fly_entail_wit_2 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= q_size_pre) |] 
  &&  [| ((s + (Znth i lv 0) ) = (sum ((sublist (0) ((i + 1 )) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
.

Definition will_it_fly_return_wit_1 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (s <= w_pre) |] 
  &&  [| (i >= q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| (problem_72_spec_z lv w_pre 1 ) |]
  &&  (IntArray.full q_pre q_size_pre lv )
.

Definition will_it_fly_return_wit_2 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (s > w_pre) |] 
  &&  [| (i >= q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| (problem_72_spec_z lv w_pre 0 ) |]
  &&  (IntArray.full q_pre q_size_pre lv )
.

Definition will_it_fly_return_wit_3 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| (problem_72_spec_z lv w_pre 0 ) |]
  &&  (IntArray.full q_pre q_size_pre lv )
.

Definition will_it_fly_partial_solve_wit_1 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (((q_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i q_pre i 0 q_size_pre lv )
.

Definition will_it_fly_partial_solve_wit_2 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (((q_pre + (((q_size_pre - 1 ) - i ) * sizeof(INT) ) )) # Int  |-> (Znth ((q_size_pre - 1 ) - i ) lv 0))
  **  (IntArray.missing_i q_pre ((q_size_pre - 1 ) - i ) 0 q_size_pre lv )
.

Definition will_it_fly_partial_solve_wit_3 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |] 
  &&  [| (q_size_pre = (Zlength (lv))) |] 
  &&  [| (problem_72_pre_z lv w_pre ) |] 
  &&  [| (will_it_fly_int_range lv ) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |]
  &&  (((q_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i q_pre i 0 q_size_pre lv )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_will_it_fly_safety_wit_1 : will_it_fly_safety_wit_1.
Axiom proof_of_will_it_fly_safety_wit_2 : will_it_fly_safety_wit_2.
Axiom proof_of_will_it_fly_safety_wit_3 : will_it_fly_safety_wit_3.
Axiom proof_of_will_it_fly_safety_wit_4 : will_it_fly_safety_wit_4.
Axiom proof_of_will_it_fly_safety_wit_5 : will_it_fly_safety_wit_5.
Axiom proof_of_will_it_fly_safety_wit_6 : will_it_fly_safety_wit_6.
Axiom proof_of_will_it_fly_safety_wit_7 : will_it_fly_safety_wit_7.
Axiom proof_of_will_it_fly_safety_wit_8 : will_it_fly_safety_wit_8.
Axiom proof_of_will_it_fly_safety_wit_9 : will_it_fly_safety_wit_9.
Axiom proof_of_will_it_fly_safety_wit_10 : will_it_fly_safety_wit_10.
Axiom proof_of_will_it_fly_entail_wit_1 : will_it_fly_entail_wit_1.
Axiom proof_of_will_it_fly_entail_wit_2 : will_it_fly_entail_wit_2.
Axiom proof_of_will_it_fly_return_wit_1 : will_it_fly_return_wit_1.
Axiom proof_of_will_it_fly_return_wit_2 : will_it_fly_return_wit_2.
Axiom proof_of_will_it_fly_return_wit_3 : will_it_fly_return_wit_3.
Axiom proof_of_will_it_fly_partial_solve_wit_1 : will_it_fly_partial_solve_wit_1.
Axiom proof_of_will_it_fly_partial_solve_wit_2 : will_it_fly_partial_solve_wit_2.
Axiom proof_of_will_it_fly_partial_solve_wit_3 : will_it_fly_partial_solve_wit_3.

End VC_Correct.
