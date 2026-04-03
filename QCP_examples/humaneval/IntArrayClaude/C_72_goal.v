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

(*----- Function will_it_fly -----*)

Definition will_it_fly_safety_wit_1 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) ,
  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
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
forall (w_pre: Z) (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
|--
  [| (((q_size_pre - 1 ) - i ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= ((q_size_pre - 1 ) - i )) |]
.

Definition will_it_fly_safety_wit_4 := 
forall (w_pre: Z) (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
|--
  [| ((q_size_pre - 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (q_size_pre - 1 )) |]
.

Definition will_it_fly_safety_wit_5 := 
forall (w_pre: Z) (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition will_it_fly_safety_wit_6 := 
forall (w_pre: Z) (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition will_it_fly_safety_wit_7 := 
forall (w_pre: Z) (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
|--
  [| ((s + (Znth i lv 0) ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (s + (Znth i lv 0) )) |]
.

Definition will_it_fly_safety_wit_8 := 
forall (w_pre: Z) (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> (s + (Znth i lv 0) ))
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition will_it_fly_safety_wit_9 := 
forall (w_pre: Z) (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (s > w_pre) |] 
  &&  [| (i >= q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.full q q_size_pre lv )
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition will_it_fly_safety_wit_10 := 
forall (w_pre: Z) (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (s <= w_pre) |] 
  &&  [| (i >= q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (IntArray.full q q_size_pre lv )
  **  ((( &( "w" ) )) # Int  |-> w_pre)
  **  ((( &( "q_size" ) )) # Int  |-> q_size_pre)
|--
  [| (1 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 1) |]
.

Definition will_it_fly_entail_wit_1 := 
forall (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) ,
  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q_pre q_size_pre lv )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (0 = (sum ((sublist (0) (0) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < 0)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q_pre q_size_pre lv )
.

Definition will_it_fly_entail_wit_2 := 
forall (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= q_size_pre) |] 
  &&  [| ((s + (Znth i lv 0) ) = (sum ((sublist (0) ((i + 1 )) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < (i + 1 ))) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
.

Definition will_it_fly_return_wit_1 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) <> (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_4 )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
|--
  (EX (k: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < q_size_pre) |] 
  &&  [| ((Znth (k) (lv) (0)) <> (Znth (((q_size_pre - 1 ) - k )) (lv) (0))) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
  ||
  ([| (0 = 0) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_size_pre)) -> ((Znth (k_2) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_2 )) (lv) (0)))) |] 
  &&  [| ((sum (lv)) > w_pre) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
  ||
  ([| (0 <> 0) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_size_pre)) -> ((Znth (k_3) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_3 )) (lv) (0)))) |] 
  &&  [| ((sum (lv)) <= w_pre) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
.

Definition will_it_fly_return_wit_2 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (s > w_pre) |] 
  &&  [| (i >= q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_4 )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
|--
  (EX (k: Z) ,
  [| (0 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < q_size_pre) |] 
  &&  [| ((Znth (k) (lv) (0)) <> (Znth (((q_size_pre - 1 ) - k )) (lv) (0))) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
  ||
  ([| (0 = 0) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_size_pre)) -> ((Znth (k_2) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_2 )) (lv) (0)))) |] 
  &&  [| ((sum (lv)) > w_pre) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
  ||
  ([| (0 <> 0) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_size_pre)) -> ((Znth (k_3) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_3 )) (lv) (0)))) |] 
  &&  [| ((sum (lv)) <= w_pre) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
.

Definition will_it_fly_return_wit_3 := 
forall (w_pre: Z) (q_size_pre: Z) (q_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (s <= w_pre) |] 
  &&  [| (i >= q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_4 )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
|--
  (EX (k: Z) ,
  [| (1 = 0) |] 
  &&  [| (0 <= k) |] 
  &&  [| (k < q_size_pre) |] 
  &&  [| ((Znth (k) (lv) (0)) <> (Znth (((q_size_pre - 1 ) - k )) (lv) (0))) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
  ||
  ([| (1 = 0) |] 
  &&  [| forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < q_size_pre)) -> ((Znth (k_2) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_2 )) (lv) (0)))) |] 
  &&  [| ((sum (lv)) > w_pre) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
  ||
  ([| (1 <> 0) |] 
  &&  [| forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < q_size_pre)) -> ((Znth (k_3) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k_3 )) (lv) (0)))) |] 
  &&  [| ((sum (lv)) <= w_pre) |]
  &&  (IntArray.full q_pre q_size_pre lv ))
.

Definition will_it_fly_partial_solve_wit_1 := 
forall (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
|--
  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (((q + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i q i 0 q_size_pre lv )
.

Definition will_it_fly_partial_solve_wit_2 := 
forall (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
|--
  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (((q + (((q_size_pre - 1 ) - i ) * sizeof(INT) ) )) # Int  |-> (Znth ((q_size_pre - 1 ) - i ) lv 0))
  **  (IntArray.missing_i q ((q_size_pre - 1 ) - i ) 0 q_size_pre lv )
.

Definition will_it_fly_partial_solve_wit_3 := 
forall (q_size_pre: Z) (lv: (@list Z)) (q: Z) (s: Z) (i: Z) ,
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (IntArray.full q q_size_pre lv )
|--
  [| ((Znth i lv 0) = (Znth ((q_size_pre - 1 ) - i ) lv 0)) |] 
  &&  [| (i < q_size_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= q_size_pre) |] 
  &&  [| (s = (sum ((sublist (0) (i) (lv))))) |] 
  &&  [| forall (k: Z) , (((0 <= k) /\ (k < i)) -> ((Znth (k) (lv) (0)) = (Znth (((q_size_pre - 1 ) - k )) (lv) (0)))) |] 
  &&  [| (0 <= q_size_pre) |] 
  &&  [| (q_size_pre < INT_MAX) |]
  &&  (((q + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i q i 0 q_size_pre lv )
.

Module Type VC_Correct.

Include common_Strategy_Correct.
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
